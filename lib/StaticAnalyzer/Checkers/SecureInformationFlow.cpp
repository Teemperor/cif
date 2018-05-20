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

class SecurityClass {
  std::set<std::string> Owners;
public:
  SecurityClass() {
  }

  static SecurityClass parse(StringRef S) {
    SecurityClass Result;
    if (S.empty())
      return Result;
    llvm::SmallVector<StringRef, 4> OwnerStrings;
    StringRef(S).split(OwnerStrings, ',');
    for (StringRef OwnerString : OwnerStrings) {
      Result.Owners.insert(OwnerString.str());
    }
    return Result;
  }

  static SecurityClass parseLabel(StringRef S) {
    auto Parts = S.split('|');
    if (Parts.first == "InfoFlow") {
      return parse(Parts.second);
    }
    return SecurityClass();
  }

  void mergeWith(const SecurityClass &Other) {
    for (auto &O : Other.Owners) {
      Owners.insert(O);
    }
  }

  bool allowsFlowFrom(const SecurityClass &Other) {
    for (auto &O : Other.Owners) {
      if (Owners.find(O) == Owners.end())
        return false;
    }
    return true;
  }

  std::string getLabel() const {
    if (Owners.empty())
      return "<NO-LABEL>";
    return llvm::join(Owners, ",");
  }

  operator bool() const {
    return !Owners.empty();
  }

  void dump() const {
    llvm::errs() << "SecurityClass: " << getLabel() << "\n";
  }
};

class SecurityContext {
  std::vector<std::pair<SecurityClass, Stmt *> > Context;
  SecurityClass ContextClass;
public:
  SecurityContext() = default;
  void add(SecurityClass NewClass, Stmt *Cause) {
    Context.emplace_back(NewClass, Cause);
    ContextClass.mergeWith(NewClass);
  }

  SecurityClass getClass() const {
    return ContextClass;
  }
};

class SecureInformationFlow
    : public Checker<check::EndOfTranslationUnit> {
  mutable std::unique_ptr<BugType> BT_Exact;

  struct Violation {
    Stmt *ViolatingStmt;
    Stmt *Source;
    SecurityClass TargetClass, SourceClass;
    SourceRange TargetLoc, SourceLoc;
  };
  std::vector<Violation> Violations;

  std::unordered_map<const Decl *, bool> PureDecls;

  void markAsPure(const Decl *D, bool IsPure = true) {
    if (!D)
      return;
    if (const FunctionTemplateDecl *TFD = dyn_cast<const FunctionTemplateDecl>(D)) {
      for (const auto &Spez : TFD->specializations())
        markAsPure(Spez);
    }
    if (const ClassTemplateDecl *TD = dyn_cast<const ClassTemplateDecl>(D)) {
      for (const auto &Spez : TD->specializations())
        markAsPure(Spez);
    }
    PureDecls[D->getCanonicalDecl()] = IsPure;
  }

  bool isPureByAttrImpl(const Decl *D) {
    bool Result = false;
    auto Attrs = D->specific_attrs<AnnotateAttr>();
    for (const auto &A : Attrs) {
      StringRef AS = A->getAnnotation();
      Result |= (AS == "InfoFlow-Pure");
    }
    return Result;
  }

  bool isPureByAttr(const Decl *D) {
    if (const FunctionDecl *FD = dyn_cast<const FunctionDecl>(D)) {
      for (const auto &Redecl : D->redecls()) {
        if (isPureByAttrImpl(Redecl))
          return true;
      }
    }
    return isPureByAttrImpl(D);
  }

  bool isPure(const Decl *D) {
    if (D == nullptr)
      return false;
    auto CD = D->getCanonicalDecl();
    auto It = PureDecls.find(CD);
    if (It != PureDecls.end()) {
      return It->second;
    }
    bool Result;
    markAsPure(D, Result = isPureByAttr(D));
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

  void foreachParamRedecl(const ParmVarDecl *D, std::function<void(const ParmVarDecl*)> Func) {
    auto C = D->getDeclContext();
    const FunctionDecl *const FD = dyn_cast_or_null<const FunctionDecl>(C);
    if (FD) {
      unsigned ParamIndex = 0;
      bool FoundParam = false;
      for(; ParamIndex < FD->getNumParams(); ++ParamIndex) {
        auto TestParam = FD->getParamDecl(ParamIndex);
        if (TestParam == D) {
          FoundParam = true;
          break;
        }
      }
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

  bool isOutParam(const ParmVarDecl *D) {
    if (D == nullptr)
      return false;

    bool Result = false;
    foreachParamRedecl(D, [&Result](const ParmVarDecl *Other) {
      auto Attrs = Other->specific_attrs<AnnotateAttr>();
      for (const auto &A : Attrs) {
        StringRef AS = A->getAnnotation();
        Result |= (AS == "InfoFlow-Out");
      }
    });
    return Result;
  }

  SecurityClass getSecurityClassAttrs(const Decl *D) {
    SecurityClass Result;
    auto Attrs = D->specific_attrs<AnnotateAttr>();
    for (const auto &A : Attrs) {
      StringRef AS = A->getAnnotation();
      Result.mergeWith(SecurityClass::parseLabel(AS.str()));
    }
    return Result;
  }

  SecurityClass getSecurityClass(const Decl *D, bool CheckRedecls = true) {
    if (D == nullptr)
      return SecurityClass();

    SecurityClass Result = getSecurityClassAttrs(D);

    if (const ParmVarDecl *PD = dyn_cast<const ParmVarDecl>(D)) {
      if (CheckRedecls) {
        foreachParamRedecl(PD, [&Result, this](const ParmVarDecl *OtherP){
          Result.mergeWith(getSecurityClass(OtherP, /*CheckRedecls*/false));
        });
      }
    }
    if (const CXXMethodDecl *MD = dyn_cast<const CXXMethodDecl>(D)) {
      Result.mergeWith(getSecurityClass(MD->getParent()));
    }
    if (const FieldDecl *FD = dyn_cast<const FieldDecl>(D)) {
      Result.mergeWith(getSecurityClass(FD->getParent()));
    }
    if (const CXXRecordDecl *RD = dyn_cast<const CXXRecordDecl>(D)) {
      if (CheckRedecls) {
        for(const auto &Redecl : RD->redecls()) {
          Result.mergeWith(getSecurityClass(Redecl, /*CheckRedecls*/false));
        }
      }
      for (auto &Base : RD->bases()) {
        TypeSourceInfo *T = Base.getTypeSourceInfo();
        const CXXRecordDecl *BaseDecl = T->getType().getTypePtrOrNull()->getAsCXXRecordDecl();
        Result.mergeWith(getSecurityClass(BaseDecl));
      }
    }
    if (const VarDecl *VD = dyn_cast<VarDecl>(D)) {
      Result.mergeWith(getSecurityClass(VD->getType()->getAsCXXRecordDecl()));
      Result.mergeWith(getSecurityClass(VD->getType()->getPointeeCXXRecordDecl()));
    }
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

  SecurityClass getSecurityClass(Stmt *S) {
    if (S == nullptr)
      return SecurityClass();

    SecurityClass Result;

    switch(S->getStmtClass()) {
      case Stmt::StmtClass::BinaryOperatorClass: {
        BinaryOperator *BO = dyn_cast<BinaryOperator>(S);
        DeclassifyInfo D = tryAsDeclassify(BO);
        if (D.valid()) {
          return D.getToClass();
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

  class DeclassifyInfo {
    SecurityClass From;
    SecurityClass To;
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
        Result.To = SecurityClass::parse(Parts.second);

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
    SecurityClass getToClass() const {
      return To;
    }

    Stmt *getChild() const {
      return Child;
    }

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
