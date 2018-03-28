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
  std::string Owner;
  bool Invalid = false;
public:
  SecurityClass() {
  }
  static SecurityClass parse(StringRef S) {
    SecurityClass Result;
    auto Parts = S.split('|');
    if (Parts.first == "InfoFlow") {
      Result.Owner = Parts.second.str();
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
      Owner.clear();
      return;
    }

    if (Owner.empty())
      Owner = Other.Owner;
    else if (!Other.Owner.empty()) {
      Invalid = true;
      Owner.clear();
      std::cerr << "non-matching labels" << std::endl;
    }
  }

  bool allowsFlowFrom(const SecurityClass &Other) {
    if (Other.Owner.empty())
      return true;
    return Owner == Other.Owner;
  }

  std::string getLabel() const {
    if (Owner.empty())
      return "<NO-LABEL>";
    return Owner;
  }

  operator bool() const {
    return !Owner.empty();
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

  bool assertAccess(Decl *Target, Stmt *Source, Stmt *ViolatingStmt) {
    Target->dumpColor();
    SecurityClass TargetClass = getSecurityClass(Target);
    SecurityClass SourceClass = getSecurityClass(Source);
    TargetClass.dump();
    SourceClass.dump();
    std::cerr << "Checking for violation " << std::endl;
    if (!TargetClass.allowsFlowFrom(SourceClass)) {
      std::cerr << "Found violation" << std::endl;
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
        std::cerr << "Found ref" << std::endl;
        return getSecurityClass(E->getFoundDecl());
      }
      default: break;
    }

    SecurityClass Result;
    for (Stmt *C : S->children()) {
      Result.mergeWith(getSecurityClass(C));
    }
    return Result;
  }

  void analyzeStmt(Stmt *S) {
    if (S == nullptr)
      return;

    switch(S->getStmtClass()) {
      case Stmt::StmtClass::DeclStmtClass: {
        DeclStmt *DS = dyn_cast<DeclStmt>(S);
        Decl *D = DS->getSingleDecl();
        if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
          assertAccess(VD,  VD->getInit(), S);
          analyzeStmt(VD->getInit());
        }
        break;
      }
      default:
        for (Stmt *C : S->children()) {
          analyzeStmt(C);
        }
        break;
    }
  }

public:
  void analyzeFunction(FunctionDecl &FD) {
    analyzeStmt(FD.getBody());
  }

  void checkEndOfTranslationUnit(const TranslationUnitDecl *TU,
                                 AnalysisManager &Mgr, BugReporter &BR) const;

  /// Reports all clones to the user.
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

  ForwardToFlowChecker A(*const_cast<SecureInformationFlow *>(this));
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
        + V.TargetClass.getLabel();
    auto R = llvm::make_unique<BugReport>(*BT_Exact, Msg,
                                          makeLocation(V.ViolatingStmt, Mgr));
    R->addRange(V.TargetLoc);

    std::string Note = std::string("from label ") + V.SourceClass.getLabel();
    R->addNote(Note, makeLocation(V.Source, Mgr), V.SourceLoc);
    BR.emitReport(std::move(R));
  }
}

//===----------------------------------------------------------------------===//
// Register SecureInformationFlow
//===----------------------------------------------------------------------===//

void ento::registerSecureInformationFlow(CheckerManager &Mgr) {
  Mgr.registerChecker<SecureInformationFlow>();
}
