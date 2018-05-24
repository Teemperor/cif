//===--- SecureInformationFlow.cpp - Clone detection checker -------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// SecureInformationFlow is a checker that reports clones in the current translation
/// unit.
///
//===----------------------------------------------------------------------===//

#include <unordered_map>
#include <unordered_set>

#include "ClangSACheckers.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/AnalysisManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

using namespace clang;
using namespace ento;

namespace {

/// A security class, consisting of a set of labels.
class SecurityClass {
  /// The set of owners of
  std::set<std::string> Owners;
public:
  SecurityClass() = default;

  /// Parses the given string into a security class. The format is a
  /// comma-separated list of owners.
  /// Example input is "A,B" which would create a security class with the owners
  /// A and B.
  static SecurityClass parse(StringRef S) {
    SecurityClass Result;
    // Empty string means an empty security class.
    if (S.empty())
      return Result;
    // Split the string into its owners and add each owner to the result.
    llvm::SmallVector<StringRef, 4> OwnerStrings;
    StringRef(S).split(OwnerStrings, ',');
    for (StringRef OwnerString : OwnerStrings) {
      Result.Owners.insert(OwnerString.str());
    }
    return Result;
  }

  /// Parses the given CIFLabel in the format:
  ///    InfoFlow|OWNERS
  /// where OWNERS is a list of owners as described in SecurityClass::parse.
  static SecurityClass parseLabel(StringRef S) {
    auto Parts = S.split('|');
    // If the prefix is our InfoFlow label, then parse the owners.
    if (Parts.first == "InfoFlow") {
      return parse(Parts.second);
    }
    // Otherwise just return an empty security class as this was not a
    // Cif label.
    return SecurityClass();
  }

  /// Merges this security class with the given security class. The new security
  /// class will be the least-restrictive security class that can hold all
  /// information from both this label and the other.
  void mergeWith(const SecurityClass &Other) {
    for (auto &O : Other.Owners) {
      Owners.insert(O);
    }
  }

  /// Returs true if it is allowed by the Cif information flow security that
  /// data with the given label can flow to this label.
  bool allowsFlowFrom(const SecurityClass &Other) {
    // The owners of the given security class needs to be a subset of the
    // current class that the flow is allowed.
    for (auto &O : Other.Owners) {
      if (Owners.find(O) == Owners.end())
        return false;
    }
    return true;
  }

  /// Returns a human-readable string representation of this security class.
  std::string getLabel() const {
    if (Owners.empty())
      return "<NO-LABEL>";
    return llvm::join(Owners, ",");
  }

  /// Returns true if this security class is not the "bottom" security class
  /// representing unclassified data.
  operator bool() const {
    return !Owners.empty();
  }

  /// Dumps the information about this security class to the LLVM error stream.
  /// For debugging purposes.
  void dump() const {
    llvm::errs() << "SecurityClass: " << getLabel() << "\n";
  }
};

/// The security context in which a statement can evaluated.
///
/// The context contains additional security classes for any data evaluated in
/// the current state of the program. A context can get a more restrictive
/// security class by implicit flows that depend on classified information.
class SecurityContext {
  std::vector<std::pair<SecurityClass, Stmt *> > Context;
  SecurityClass ContextClass;
public:
  SecurityContext() = default;
  /// Adds the given security class to the context. This will increase the
  /// security class of the context to the least-restrictive class that
  /// can hold information from the new class and the existing context class.
  void add(SecurityClass NewClass, Stmt *Cause) {
    Context.emplace_back(NewClass, Cause);
    ContextClass.mergeWith(NewClass);
  }

  /// Returns the security class of the context that should be additionally
  /// applied to every information evaluated in this context.
  SecurityClass getClass() const {
    return ContextClass;
  }
};

/// Implements the Cif secure information flow policy.
class SecureInformationFlow
    : public Checker<check::EndOfTranslationUnit> {
  mutable std::unique_ptr<BugType> BT_Exact;

  /// A violation of the policy that was found in the program while verifying.
  struct Violation {
    /// The statement that is violating the policy.
    Stmt *ViolatingStmt;
    /// The source of the information that violated the information flow. May
    /// be null in case the source of the information is not clear.
    Stmt *Source;
    SecurityClass TargetClass, SourceClass;
    SourceRange TargetLoc, SourceLoc;
  };
  /// A list of all found violations by the verifier.
  std::vector<Violation> Violations;

  /// A map of decls to a flag that designed whether they are pure or not.
  std::unordered_map<const Decl *, bool> PureDecls;

  /// Marks the given decl as pure (or as not pure).
  void markAsPure(const Decl *D, bool IsPure = true) {
    // No decl given means no work to do.
    if (!D)
      return;
    // For function template decls we also mark all specializations as pure.
    if (const FunctionTemplateDecl *TFD = dyn_cast<const FunctionTemplateDecl>(D)) {
      for (const auto &Spez : TFD->specializations())
        markAsPure(Spez);
    }
    // Same for class templates.
    if (const ClassTemplateDecl *TD = dyn_cast<const ClassTemplateDecl>(D)) {
      for (const auto &Spez : TD->specializations())
        markAsPure(Spez);
    }
    // Mark the canonical decl as pure.
    PureDecls[D->getCanonicalDecl()] = IsPure;
  }

  /// Returns if the given decl has a attribute designating as 'pure' in the
  /// Cif information policy model. Doesn't check redecls.
  bool isPureByAttrImpl(const Decl *D) {
    bool Result = false;
    auto Attrs = D->specific_attrs<AnnotateAttr>();
    for (const auto &A : Attrs) {
      StringRef AS = A->getAnnotation();
      Result |= (AS == "InfoFlow-Pure");
    }
    return Result;
  }
  /// Returns if the given decl has a attribute designating as 'pure' in the
  /// Cif information policy model.
  bool isPureByAttr(const Decl *D) {
    // Walk over all redecls. For now we only support functions.
    if (const FunctionDecl *FD = dyn_cast<const FunctionDecl>(D)) {
      for (const auto &Redecl : D->redecls()) {
        if (isPureByAttrImpl(Redecl))
          return true;
      }
    }
    return isPureByAttrImpl(D);
  }

  /// Return true if the given decl is pure.
  bool isPure(const Decl *D) {
    if (D == nullptr)
      return false;
    // We look up the canonical decl in the PureDecls map. If we found a result,
    // we return it.
    auto CD = D->getCanonicalDecl();
    auto It = PureDecls.find(CD);
    if (It != PureDecls.end()) {
      return It->second;
    }
    // Otherwise we manually look up this decl and cache the result in the
    // PureDecl.
    bool Result;
    markAsPure(CD, Result = isPureByAttr(CD));
    return Result;
  }


  bool assertAccess(const SecurityContext &Ctxt, Stmt *ViolatingStmt,
                    SecurityClass TargetClass, SourceRange TargetRange,
                    SecurityClass SourceClass, SourceRange SourceRange) {
    SourceClass.mergeWith(Ctxt.getClass());
    if (!TargetClass.allowsFlowFrom(SourceClass)) {
      Violations.push_back({ViolatingStmt, nullptr, TargetClass, SourceClass,
                              TargetRange, SourceRange});
      return false;
    }
    return true;
  }

  bool assertAccess(const SecurityContext &Ctxt,
                    SecurityClass TargetClass, SourceRange TargetRange,
                    Stmt *Source, Stmt *ViolatingStmt) {
    if (ViolatingStmt == nullptr)
      return true;

    SecurityClass SourceClass = getSecurityClass(Source);
    SourceClass.mergeWith(Ctxt.getClass());

    if (!TargetClass.allowsFlowFrom(SourceClass)) {
      Violations.push_back({ViolatingStmt, Source, TargetClass, SourceClass,
                              TargetRange, Source->getSourceRange()});
      return false;
    }
    return true;
  }

  bool assertAccess(const SecurityContext &Ctxt, Decl *Target, Stmt *Source, Stmt *ViolatingStmt) {
    return assertAccess(Ctxt, getSecurityClass(Target), Target->getSourceRange(),
                        Source, ViolatingStmt);
  }

  bool assertAccess(const SecurityContext &Ctxt, Decl *Target, Stmt *Source) {
    return assertAccess(Ctxt, getSecurityClass(Target), Target->getSourceRange(),
                        Source, Source);
  }


  bool assertAccess(const SecurityContext &Ctxt, Stmt *Target, Stmt *Source, Stmt *ViolatingStmt) {
    return assertAccess(Ctxt, getSecurityClass(Target), Target->getSourceRange(),
                        Source, ViolatingStmt);
  }

  /// Iterates over each redecl of the given ParmVarDecl.
  void foreachParamRedecl(const ParmVarDecl *D, std::function<void(const ParmVarDecl*)> Func) {
    auto C = D->getDeclContext();
    const FunctionDecl *const FD = dyn_cast_or_null<const FunctionDecl>(C);
    // First check if the param was declared in a function.
    if (FD) {
      // Find the index of the given parameter in its parent function.
      unsigned ParamIndex = 0;
      bool FoundParam = false;
      for(; ParamIndex < FD->getNumParams(); ++ParamIndex) {
        auto TestParam = FD->getParamDecl(ParamIndex);
        if (TestParam == D) {
          FoundParam = true;
          break;
        }
      }
      // If we found a valid parameter index, we iterate over all redecls and
      // call our function on it.
      if (FoundParam) {
        for (const FunctionDecl *Redecl : FD->redecls()) {
          if (ParamIndex < Redecl->getNumParams()) {
            auto RedeclParam = Redecl->getParamDecl(ParamIndex);
            Func(RedeclParam);
          }
        }
      }
    }
  }

  /// Whether this parameter is a 'out' parameter in the Cif information flow
  /// policy.
  bool isOutParam(const ParmVarDecl *D) {
    if (D == nullptr)
      return false;

    bool Result = false;
    // Iterate over each redecl of this parameter to search for the attribute.
    foreachParamRedecl(D, [&Result](const ParmVarDecl *Other) {
      auto Attrs = Other->specific_attrs<AnnotateAttr>();
      // If any attribute has the "InfoFlow-Out" text, we know that the user
      // has marked this as a pure out parameter.
      for (const auto &A : Attrs) {
        StringRef AS = A->getAnnotation();
        Result |= (AS == "InfoFlow-Out");
      }
    });
    return Result;
  }

  /// Parses the attributes of the given decl for a security class.
  SecurityClass getSecurityClassAttrs(const Decl *D) {
    SecurityClass Result;
    auto Attrs = D->specific_attrs<AnnotateAttr>();
    for (const auto &A : Attrs) {
      StringRef AS = A->getAnnotation();
      Result.mergeWith(SecurityClass::parseLabel(AS.str()));
    }
    return Result;
  }

  /// Returns the security class of the given decl.
  /// The CheckRedecls parameter is used when the caller does not want to visit
  /// all the redecls to determine the security class (for example because the
  /// caller is already iterating over the redecls and we don't want infinite
  /// recursion).
  SecurityClass getSecurityClass(const Decl *D, bool CheckRedecls = true) {
    if (D == nullptr)
      return SecurityClass();

    // First get the security class of the decl itself by reading its
    // attributes.
    SecurityClass Result = getSecurityClassAttrs(D);

    // Now we handle all the special cases.

    // For parameter decls we have to check all redecls.
    if (const ParmVarDecl *PD = dyn_cast<const ParmVarDecl>(D)) {
      if (CheckRedecls) {
        foreachParamRedecl(PD, [&Result, this](const ParmVarDecl *OtherP){
          Result.mergeWith(getSecurityClass(OtherP, /*CheckRedecls*/false));
        });
      }
    }
    // For method decls, we merge the security class of the class with the
    // security class of the return value.
    if (const CXXMethodDecl *MD = dyn_cast<const CXXMethodDecl>(D)) {
      Result.mergeWith(getSecurityClass(MD->getParent()));
    }
    // The security class of a field decl also contains the security class of
    // the class.
    if (const FieldDecl *FD = dyn_cast<const FieldDecl>(D)) {
      Result.mergeWith(getSecurityClass(FD->getParent()));
    }

    if (const CXXRecordDecl *RD = dyn_cast<const CXXRecordDecl>(D)) {
      // Check the security classes of all redecls.
      if (CheckRedecls) {
        for(const auto &Redecl : RD->redecls()) {
          Result.mergeWith(getSecurityClass(Redecl, /*CheckRedecls*/false));
        }
      }
      // Check the security classes of the base classes.
      for (auto &Base : RD->bases()) {
        TypeSourceInfo *T = Base.getTypeSourceInfo();
        const CXXRecordDecl *BaseDecl = T->getType().getTypePtrOrNull()->getAsCXXRecordDecl();
        Result.mergeWith(getSecurityClass(BaseDecl));
      }
    }
    // Variable decls inherit he security classes of the used record and for
    // pointers the pointee record.
    if (const VarDecl *VD = dyn_cast<VarDecl>(D)) {
      Result.mergeWith(getSecurityClass(VD->getType()->getAsCXXRecordDecl()));
      Result.mergeWith(getSecurityClass(VD->getType()->getPointeeCXXRecordDecl()));
    }
    // Generic redecl check code.
    // FIXME: Is this redundant with above's redecl walking code?
    if (CheckRedecls) {
      const Decl *Redecl = D->getMostRecentDecl();
      do {
        // Don't redecl check the previous decl, otherwise we just keep
        // keep recursively checking the redecl chain.
        Result.mergeWith(getSecurityClass(Redecl, /*CheckRedecls*/false));
        if (Redecl->isFirstDecl())
          break;
      } while ((Redecl = Redecl->getPreviousDecl()));
    }
    return Result;
  }

  // Gets the security class of the given stmt.
  SecurityClass getSecurityClass(Stmt *S) {
    if (S == nullptr)
      return SecurityClass();

    SecurityClass Result;

    switch(S->getStmtClass()) {
      case Stmt::StmtClass::BinaryOperatorClass: {
        BinaryOperator *BO = dyn_cast<BinaryOperator>(S);
        DeclassifyInfo D = tryAsDeclassify(BO);
        if (D.valid()) {
          return D.getTargetClass();
        }
        break;
      }
      case Stmt::StmtClass::DeclRefExprClass: {
        DeclRefExpr *E = dyn_cast<DeclRefExpr>(S);
        return getSecurityClass(E->getFoundDecl());
      }
      case Stmt::StmtClass::MemberExprClass: {
        MemberExpr *E = dyn_cast<MemberExpr>(S);
        Result = getSecurityClass(E->getFoundDecl().getDecl());
        break;
      }
      case Stmt::StmtClass::CXXMemberCallExprClass: {
        CXXMemberCallExpr *E = dyn_cast<CXXMemberCallExpr>(S);

        auto S = SecurityClass();
        auto CalleeClass = getSecurityClass(E->getCallee());
        auto MethodClass = getSecurityClass(E->getMethodDecl());
        if (isPure(E->getRecordDecl())) {
          return CalleeClass;
        } else {
          return MethodClass;
        }

        return S;
      }
      case Stmt::StmtClass::CallExprClass: {
        CallExpr *E = dyn_cast<CallExpr>(S);
        if (isPure(E->getCalleeDecl()))
          break;
        return getSecurityClass(E->getCalleeDecl());
      }
      default: break;
    }

    for (Stmt *C : S->children()) {
      Result.mergeWith(getSecurityClass(C));
    }
    return Result;
  }

  // Information about a declassify call. A declassify call moves information
  // from one security class to another.
  class DeclassifyInfo {
    SecurityClass From;
    SecurityClass Target;
    Stmt *S = nullptr;
    Stmt *Child = nullptr;
    bool Valid = false;
    std::string Error;
  public:
    DeclassifyInfo() = default;
    static DeclassifyInfo parse(Stmt *S, Stmt *Child, StringRef Str) {
      DeclassifyInfo Result;
      Result.S = S;
      Result.Child = Child;

      auto Parts = Str.split("->");
      if (Parts.second.empty() && !Str.endswith("->")) {
        Result.Error = "Couldn't parse declassify: " + Str.str();
        abort();
      } else {
        Result.From = SecurityClass::parse(Parts.first);
        Result.Target = SecurityClass::parse(Parts.second);

        Result.Valid = true;
      }

      return Result;
    }

    bool valid() const {
      return Valid;
    }

    bool hasError() const {
      return !Error.empty();
    }

    std::string getError() const {
      return Error;
    }

    SecurityClass getFromClass() const {
      return From;
    }
    SecurityClass getTargetClass() const {
      return Target;
    }

    // The source statement that is the input data with the expected 'From'
    // security class.
    Stmt *getChild() const {
      return Child;
    }

    // Returns the declassify statement itself.
    Stmt *getStmt() const {
      return S;
    }
  };

  DeclassifyInfo tryAsDeclassify(Stmt *S) {
    if (BinaryOperator *BO = dyn_cast_or_null<BinaryOperator>(S)) {
      if (BO->getOpcode() != BinaryOperatorKind::BO_Comma)
        return DeclassifyInfo();
      Expr *LHS = BO->getLHS();
      if (CStyleCastExpr *C = dyn_cast<CStyleCastExpr>(LHS)) {
        Expr *Content = C->getSubExprAsWritten();
        if (StringLiteral *Str = dyn_cast_or_null<StringLiteral>(Content)) {
          return DeclassifyInfo::parse(S, BO->getRHS(), Str->getString());
        }
      }
    }
    return DeclassifyInfo();
  }

  const std::unordered_set<BinaryOperatorKind> AssignTypes = {
    BinaryOperatorKind::BO_Assign,
    BinaryOperatorKind::BO_AddAssign,
    BinaryOperatorKind::BO_AndAssign,
    BinaryOperatorKind::BO_DivAssign,
    BinaryOperatorKind::BO_MulAssign,
    BinaryOperatorKind::BO_OrAssign,
    BinaryOperatorKind::BO_RemAssign,
    BinaryOperatorKind::BO_ShlAssign,
    BinaryOperatorKind::BO_ShrAssign,
    BinaryOperatorKind::BO_SubAssign,
    BinaryOperatorKind::BO_XorAssign,
  };

  bool isAssignOp(BinaryOperatorKind K) {
    return AssignTypes.find(K) != AssignTypes.end();
  }

  bool doesReturn(const Stmt *S) {
    if (S == nullptr)
      return false;
    if (S->getStmtClass() == Stmt::ReturnStmtClass)
      return true;
    for (const Stmt *C : S->children())
      if (doesReturn(C))
        return true;
    return false;
  }

  void analyzeStmt(SecurityContext &ParentCtxt, FunctionDecl &FD, Stmt *S) {
    if (S == nullptr)
      return;
    SecurityContext Ctxt = ParentCtxt;

    switch(S->getStmtClass()) {
      case Stmt::StmtClass::IfStmtClass: {
        IfStmt *If = dyn_cast<IfStmt>(S);
        SecurityClass CondClass = getSecurityClass(If->getCond());

        SecurityContext SubContext = Ctxt;
        SubContext.add(CondClass, If->getCond());

        analyzeStmt(Ctxt, FD, If->getCond());
        analyzeStmt(SubContext, FD, If->getThen());
        analyzeStmt(SubContext, FD, If->getElse());
        if (doesReturn(If->getThen()) || doesReturn(If->getElse())) {
          ParentCtxt = SubContext;
        }
        return;
      }
      case Stmt::StmtClass::CompoundAssignOperatorClass:
      case Stmt::StmtClass::BinaryOperatorClass: {
        BinaryOperator *BO = dyn_cast<BinaryOperator>(S);
        if (isAssignOp(BO->getOpcode())) {
          assertAccess(Ctxt, BO->getLHS(), BO->getRHS(), BO);
        }
        DeclassifyInfo D = tryAsDeclassify(BO);
        if (D.valid()) {
          assertAccess(Ctxt, D.getFromClass(), D.getStmt()->getSourceRange(),
                       D.getChild(), D.getStmt());
        }
        break;
      }
      case Stmt::StmtClass::DeclStmtClass: {
        DeclStmt *DS = dyn_cast<DeclStmt>(S);
        for (Decl *CD : DS->decls()) {
          if (VarDecl *VD = dyn_cast<VarDecl>(CD)) {
            assertAccess(Ctxt, VD,  VD->getInit(), S);
          }
        }
        break;
      }
      case Stmt::StmtClass::ReturnStmtClass: {
        ReturnStmt *RS = dyn_cast<ReturnStmt>(S);
        assertAccess(Ctxt, &FD, RS->getRetValue(), RS);
        break;
      }
      case Stmt::StmtClass::CXXMemberCallExprClass: {
        CXXMemberCallExpr *Call = dyn_cast<CXXMemberCallExpr>(S);
        FunctionDecl *TargetFunc = dyn_cast_or_null<FunctionDecl>(Call->getCalleeDecl());
        if (!TargetFunc)
          break;
        const SecurityClass S = getSecurityClass(Call);
        unsigned I = 0;
        for (Expr * E : Call->arguments()) {
          ParmVarDecl *Param = nullptr;
          SourceRange ParamRange;
          if (I < TargetFunc->getNumParams()) {
            Param = TargetFunc->getParamDecl(I);
            ParamRange = Param->getSourceRange();
          } else {
            ParamRange = TargetFunc->getLocation();
          }
          SecurityClass ParamClass;
          ParamClass.mergeWith(getSecurityClass(Param));
          if (isOutParam(Param)) {
            assertAccess(Ctxt, E, getSecurityClass(E), E->getSourceRange(),
                         ParamClass, Param->getSourceRange());
          } else {
            ParamClass.mergeWith(S);
            assertAccess(Ctxt, ParamClass, ParamRange, E, E);
          }
          ++I;
        }
        break;
      }
      case Stmt::StmtClass::CallExprClass: {
        CallExpr *Call = dyn_cast<CallExpr>(S);
        FunctionDecl *TargetFunc = dyn_cast_or_null<FunctionDecl>(Call->getCalleeDecl());
        if (isPure(TargetFunc))
          break;
        unsigned I = 0;
        for (Expr * E : Call->arguments()) {
          ParmVarDecl *Param = nullptr;
          SourceRange ParamRange;
          if (TargetFunc) {
            if (I < TargetFunc->getNumParams()) {
              Param = TargetFunc->getParamDecl(I);
              ParamRange = Param->getSourceRange();
            } else {
              ParamRange = TargetFunc->getLocation();
            }
          } else {
            ParamRange = E->getSourceRange();
          }
          SecurityClass ParamClass = getSecurityClass(Param);
          if (isOutParam(Param)) {
            assertAccess(Ctxt, E, getSecurityClass(E), E->getSourceRange(),
                         ParamClass, Param->getSourceRange());
          } else {
            assertAccess(Ctxt, ParamClass, ParamRange, E, E);
          }
          ++I;
        }
        break;
      }
      default:
          break;
    }
    for (Stmt *C : S->children())
      analyzeStmt(Ctxt, FD, C);
  }

public:
  void analyzeFunction(FunctionDecl &FD) {
    SecurityContext Context;
    analyzeStmt(Context, FD, FD.getBody());
  }
  void analyseInitializer(const CXXCtorInitializer &I) {
    SecurityContext Ctxt;
    if (I.isAnyMemberInitializer()) {
      assertAccess(Ctxt, I.getAnyMember(), I.getInit());
    } else if (I.isBaseInitializer()) {
      // TODO: Can't verify this without finding what constructor
      // was called?
    }
  }

  void analyzeFieldDecl(FieldDecl *D) {
    SecurityContext Ctxt;
    assertAccess(Ctxt, D, D->getInClassInitializer());
  }

  void checkEndOfTranslationUnit(const TranslationUnitDecl *TU,
                                 AnalysisManager &Mgr, BugReporter &BR) const;

  void reportViolations(BugReporter &BR, AnalysisManager &Mgr) const;
};

class ForwardToFlowChecker
  : public RecursiveASTVisitor<ForwardToFlowChecker> {

  SecureInformationFlow &Checker;
public:
  ForwardToFlowChecker(SecureInformationFlow &Checker) : Checker(Checker) {
  }
  bool VisitFunctionDecl(FunctionDecl *D) {
    Checker.analyzeFunction(*D);
    return true;
  }
  bool VisitFieldDecl(FieldDecl *D) {
    Checker.analyzeFieldDecl(D);
    return true;
  }
  bool VisitCXXConstructorDecl(CXXConstructorDecl *D) {
    for (auto &I : D->inits()) {
      Checker.analyseInitializer(*I);
    }
    return true;
  }
};

} // end anonymous namespace

void SecureInformationFlow::checkEndOfTranslationUnit(const TranslationUnitDecl *TU,
                                             AnalysisManager &Mgr,
                                             BugReporter &BR) const {

  SecureInformationFlow *Self = const_cast<SecureInformationFlow *>(this);

  for (Decl *D : TU->decls()) {
    if (NamespaceDecl *ND = dyn_cast<NamespaceDecl>(D)) {
      if (ND->getName() == "__CIF_Unqiue_Name_Pure") {
        for (Decl *PureDecl : ND->decls()) {
          if (UsingShadowDecl *SD = dyn_cast<UsingShadowDecl>(PureDecl)) {
            Self->markAsPure(SD->getTargetDecl());
          }
        }
      }
    }
  }

  ForwardToFlowChecker A(*Self);
  A.TraverseTranslationUnitDecl(const_cast<TranslationUnitDecl *>(TU));
  reportViolations(BR, Mgr);
}

static PathDiagnosticLocation makeLocation(const Stmt *S,
                                           AnalysisManager &Mgr) {
  ASTContext &ACtx = Mgr.getASTContext();
  return PathDiagnosticLocation::createBegin(
      S, ACtx.getSourceManager(),
      Mgr.getAnalysisDeclContext(ACtx.getTranslationUnitDecl()));
}

void SecureInformationFlow::reportViolations(
    BugReporter &BR, AnalysisManager &Mgr) const {

  if (!BT_Exact)
    BT_Exact.reset(new BugType(this, "Information flow violation", "Information Flow"));

  for (Violation V : Violations) {
    std::string Msg = std::string("Information flow violation from label ")
        + V.SourceClass.getLabel() + " to label " + V.TargetClass.getLabel();
    auto R = llvm::make_unique<BugReport>(*BT_Exact, Msg,
                                          makeLocation(V.ViolatingStmt, Mgr));
    R->addRange(V.TargetLoc);
    BR.emitReport(std::move(R));
  }
}

//===----------------------------------------------------------------------===//
// Register SecureInformationFlow
//===----------------------------------------------------------------------===//

void ento::registerSecureInformationFlow(CheckerManager &Mgr) {
  Mgr.registerChecker<SecureInformationFlow>();
}
