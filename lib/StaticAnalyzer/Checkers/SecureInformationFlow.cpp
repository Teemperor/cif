﻿//===--- SecureInformationFlow.cpp - Clone detection checker -------------*- C++ -*-===//
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
    } else {
      llvm::errs() << "Parsing error\n";
      abort();
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

  void dump() {
    llvm::errs() << "SecurityClass: " << getLabel() << "\n";
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

  std::vector<const Decl *> PureDecls;

  void markAsPure(const Decl *D) {
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
    PureDecls.push_back(D->getCanonicalDecl());
  }

  bool isPure(const Decl *D) {
    if (D == nullptr)
      return false;
    auto CD = D->getCanonicalDecl();
    auto It = std::lower_bound(PureDecls.begin(), PureDecls.end(), CD);
    return It != PureDecls.end() && *It == CD;
  }

  bool assertAccess(SecurityClass TargetClass, SourceRange TargetRange,
                    Stmt *Source, Stmt *ViolatingStmt) {
    if (ViolatingStmt == nullptr)
      return true;
    SecurityClass SourceClass = getSecurityClass(Source);
    if (!TargetClass.allowsFlowFrom(SourceClass)) {
      Violations.push_back({ViolatingStmt, Source, TargetClass, SourceClass,
                              TargetRange, Source->getSourceRange()});
      return false;
    }
    return true;
  }

  bool assertAccess(Decl *Target, Stmt *Source, Stmt *ViolatingStmt) {
    return assertAccess(getSecurityClass(Target), Target->getSourceRange(),
                        Source, ViolatingStmt);
  }

  bool assertAccess(Decl *Target, Stmt *Source) {
    return assertAccess(getSecurityClass(Target), Target->getSourceRange(),
                        Source, Source);
  }


  bool assertAccess(Stmt *Target, Stmt *Source, Stmt *ViolatingStmt) {
    return assertAccess(getSecurityClass(Target), Target->getSourceRange(),
                        Source, ViolatingStmt);
  }

  SecurityClass getSecurityClass(const Decl *D, bool CheckRedecls = true) {
    if (D == nullptr)
      return SecurityClass();
    const AnnotateAttr *A = D->getAttr<AnnotateAttr>();
    SecurityClass Result;
    if (A) {
      Result.mergeWith(SecurityClass::parseLabel(A->getAnnotation().str()));
    }
    if (const ParmVarDecl *PD = dyn_cast<const ParmVarDecl>(D)) {
      auto C = PD->getDeclContext();
      const FunctionDecl *const FD = dyn_cast_or_null<const FunctionDecl>(C);
      if (CheckRedecls && FD) {
        unsigned ParamIndex = 0;
        bool FoundParam = false;
        for(; ParamIndex < FD->getNumParams(); ++ParamIndex) {
          auto TestParam = FD->getParamDecl(ParamIndex);
          if (TestParam == PD) {
            FoundParam = true;
            break;
          }
        }
        if (FoundParam) {
          for (const FunctionDecl *Redecl : FD->redecls()) {
            auto RedeclParam = Redecl->getParamDecl(ParamIndex);
            Result.mergeWith(getSecurityClass(RedeclParam, /*CheckRedecls*/false));
          }
        }
      }
    }
    if (const CXXMethodDecl *MD = dyn_cast<const CXXMethodDecl>(D)) {
      Result.mergeWith(getSecurityClass(MD->getParent()));
    }
    if (const FieldDecl *FD = dyn_cast<const FieldDecl>(D)) {
      Result.mergeWith(getSecurityClass(FD->getParent()));
    }
    if (const CXXRecordDecl *RD = dyn_cast<const CXXRecordDecl>(D)) {
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

  void analyzeStmt(FunctionDecl &FD, Stmt *S) {
    if (S == nullptr)
      return;

    switch(S->getStmtClass()) {
      case Stmt::StmtClass::CompoundAssignOperatorClass:
      case Stmt::StmtClass::BinaryOperatorClass: {
        BinaryOperator *BO = dyn_cast<BinaryOperator>(S);
        if (isAssignOp(BO->getOpcode())) {
          assertAccess(BO->getLHS(), BO->getRHS(), BO);
        }
        DeclassifyInfo D = tryAsDeclassify(BO);
        if (D.valid()) {
          assertAccess(D.getFromClass(), D.getStmt()->getSourceRange(),
                       D.getChild(), D.getStmt());
        }
        break;
      }
      case Stmt::StmtClass::DeclStmtClass: {
        DeclStmt *DS = dyn_cast<DeclStmt>(S);
        for (Decl *CD : DS->decls()) {
          if (VarDecl *VD = dyn_cast<VarDecl>(CD)) {
            assertAccess(VD,  VD->getInit(), S);
            analyzeStmt(FD, VD->getInit());
          }
        }
        break;
      }
      case Stmt::StmtClass::ReturnStmtClass: {
        ReturnStmt *RS = dyn_cast<ReturnStmt>(S);
        assertAccess(&FD, RS->getRetValue(), RS);
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
          SecurityClass ParamClass = S;
          ParamClass.mergeWith(getSecurityClass(Param));
          assertAccess(ParamClass, ParamRange, E, E);
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
          assertAccess(ParamClass, ParamRange, E, E);
          ++I;
        }
        break;
      }
      default:
          break;
    }
    for (Stmt *C : S->children())
      analyzeStmt(FD, C);
  }

public:
  void analyzeFunction(FunctionDecl &FD) {
    analyzeStmt(FD, FD.getBody());
  }
  void analyseInitializer(const CXXCtorInitializer &I) {
    if (I.isAnyMemberInitializer()) {
      assertAccess(I.getAnyMember(), I.getInit());
    } else if (I.isBaseInitializer()) {
      // TODO: Can't verify this without finding what constructor
      // was called?
    }
  }

  void analyzeFieldDecl(FieldDecl *D) {
    assertAccess(D, D->getInClassInitializer());
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
  std::sort(Self->PureDecls.begin(), Self->PureDecls.end());

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
