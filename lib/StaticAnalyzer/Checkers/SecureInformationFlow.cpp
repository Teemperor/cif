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
    auto Parts = S.split('|');
    if (Parts.first == "InfoFlow") {
      llvm::SmallVector<StringRef, 4> OwnerStrings;
      StringRef(Parts.second).split(OwnerStrings, ',');
      for (StringRef OwnerString : OwnerStrings) {
        Result.Owners.insert(OwnerString.str());
      }
    } else {
      llvm::errs() << "Parsing error\n";
      abort();
    }
    return Result;
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
    if (const FunctionTemplateDecl *TFD = dyn_cast<const FunctionTemplateDecl>(D)) {
      for (const auto &Spez : TFD->specializations())
        markAsPure(Spez);
    }
    PureDecls.push_back(D->getCanonicalDecl());
  }

  bool isPure(const Decl *D) {
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

  bool assertAccess(Stmt *Target, Stmt *Source, Stmt *ViolatingStmt) {
    return assertAccess(getSecurityClass(Target), Target->getSourceRange(),
                        Source, ViolatingStmt);
  }

  SecurityClass getSecurityClass(Decl *D) {
    if (D == nullptr)
      return SecurityClass();
    const AnnotateAttr *A = D->getAttr<AnnotateAttr>();
    if (A) {
      return SecurityClass::parse(A->getAnnotation().str());
    }
    return SecurityClass();
  }

  SecurityClass getSecurityClass(Stmt *S) {
    if (S == nullptr)
      return SecurityClass();

    SecurityClass Result;

    switch(S->getStmtClass()) {
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
        auto S = getSecurityClass(E->getCallee());
        S.mergeWith(getSecurityClass(E->getMethodDecl()));
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

  void analyzeStmt(FunctionDecl &FD, Stmt *S) {
    if (S == nullptr)
      return;

    switch(S->getStmtClass()) {
      case Stmt::StmtClass::BinaryOperatorClass: {
        BinaryOperator *BO = dyn_cast<BinaryOperator>(S);
        if (BO->getOpcode() == BinaryOperatorKind::BO_Assign) {
          assertAccess(BO->getLHS(), BO->getRHS(), BO);
        } else {
          for (Stmt *C : S->children()) {
            analyzeStmt(FD, C);
          }
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
        if (!TargetFunc)
          break;
        if (isPure(TargetFunc))
          break;
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
          SecurityClass ParamClass = getSecurityClass(Param);
          assertAccess(ParamClass, ParamRange, E, E);
          ++I;
        }
        break;
      }
      default: {
        for (Stmt *C : S->children())
          analyzeStmt(FD, C);
        break;
      }
    }
  }

public:
  void analyzeFunction(FunctionDecl &FD) {
    analyzeStmt(FD, FD.getBody());
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
    std::string Msg = std::string("Information flow violation to label ")
        + V.TargetClass.getLabel() + " from label " + V.SourceClass.getLabel();
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
