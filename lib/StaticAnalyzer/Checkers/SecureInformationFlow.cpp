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

#include <iostream>

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
  bool Invalid = false;
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
      std::cerr << "Parsing error" << std::endl;
    }
    return Result;
  }

  void mergeWith(const SecurityClass &Other) {
    if (Invalid)
      return;
    // Invalid propagates
    if (Other.Invalid) {
      Invalid = true;
      Owners.clear();
      return;
    }

    if (Owners.empty())
      Owners = Other.Owners;
    else if (!Other.Owners.empty()) {
      Invalid = true;
      Owners.clear();
      std::cerr << "non-matching labels" << std::endl;
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
    llvm::errs() << "SecurityClass: " << getLabel();

    if (Invalid)
      llvm::errs() << ", Invalid";
    llvm::errs() << "\n";
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

  std::vector<Decl *> PureFunctions;

  void markAsPure(Decl *D) {
    PureFunctions.push_back(D);
  }

  bool isPure(Decl *D) {
    auto It = std::lower_bound(PureFunctions.begin(), PureFunctions.end(), D);
    return It != PureFunctions.end() && *It == D;
  }

  bool assertAccess(Decl *Target, Stmt *Source, Stmt *ViolatingStmt) {
    SecurityClass TargetClass = getSecurityClass(Target);
    SecurityClass SourceClass = getSecurityClass(Source);
    if (!TargetClass.allowsFlowFrom(SourceClass)) {
      Violations.push_back({ViolatingStmt, Source, TargetClass, SourceClass,
                              Target->getSourceRange(),
                              Source->getSourceRange()});
      return false;
    }
    return true;
  }

  bool assertAccess(Stmt *Target, Stmt *Source, Stmt *ViolatingStmt) {
    SecurityClass TargetClass = getSecurityClass(Target);
    SecurityClass SourceClass = getSecurityClass(Source);
    if (!TargetClass.allowsFlowFrom(SourceClass)) {
      Violations.push_back({ViolatingStmt, Source, TargetClass, SourceClass,
                              Target->getSourceRange(),
                              Source->getSourceRange()});
      return false;
    }
    return true;
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

    switch(S->getStmtClass()) {
      case Stmt::StmtClass::DeclRefExprClass: {
        DeclRefExpr *E = dyn_cast<DeclRefExpr>(S);
        return getSecurityClass(E->getFoundDecl());
      }
      case Stmt::StmtClass::MemberExprClass: {
        MemberExpr *E = dyn_cast<MemberExpr>(S);
        return getSecurityClass(E->getFoundDecl().getDecl());
      }
      case Stmt::StmtClass::CallExprClass: {
        CallExpr *E = dyn_cast<CallExpr>(S);
        if (isPure(E->getCalleeDecl()))
          break;
        return getSecurityClass(E->getCalleeDecl());
      }
      default: break;
    }

    SecurityClass Result;
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
        Decl *D = DS->getSingleDecl();
        if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
          assertAccess(VD,  VD->getInit(), S);
          analyzeStmt(FD, VD->getInit());
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
        FunctionDecl *TargetFunc = dyn_cast<FunctionDecl>(Call->getCalleeDecl());
        for (unsigned I = 0; I < TargetFunc->getNumParams(); ++I) {
          assertAccess(TargetFunc->getParamDecl(I), Call->getArg(I), Call->getArg(I));
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
  std::sort(Self->PureFunctions.begin(), Self->PureFunctions.end());

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
