// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

int strcmp(const char *username, const char *password);
CIFPure int strcmp2(const char *username, const char *password);

CIFPureList {
  using ::strcmp;
}

int login1(char *username, CIFLabel("Password") char *password) {
  CIFLabel("X") int correct = strcmp(password, "letmein"); // expected-warning{{Information flow violation from label Password to label X}}
  return CIFDeclassify("X->", correct);
}

int login1Strcmp2(char *username, CIFLabel("Password") char *password) {
  CIFLabel("X") int correct = strcmp2(password, "letmein"); // expected-warning{{Information flow violation from label Password to label X}}
  return CIFDeclassify("X->", correct);
}


int login2(char *username, CIFLabel("Password") char *password) {
  CIFLabel("Password") int correct = strcmp(password, "letmein");
  return correct; // expected-warning{{Information flow violation from label Password to label <NO-LABEL>}}
}

CIFLabel("Password")
int login3(char *username, CIFLabel("Password") char *password) {
  CIFLabel("Password") int correct = strcmp(password, "letmein");
  return correct;
}

CIFLabel("Password")
int login4(char *username, CIFLabel("Password") char *password) {
  return login3(username, password);
}

int login5(char *username, CIFLabel("Password") char *password) {
  return login3(password, password); // expected-warning{{Information flow violation from label Password to label <NO-LABEL>}} \
  // expected-warning{{Information flow violation from label Password to label <NO-LABEL>}}
}

void login6(char *username, CIFLabel("Password") char *password) {
  login3(username, password);
  return;
}

void login7(char *username, CIFLabel("Password") char *password) {
  login3(password, password); // expected-warning{{Information flow violation from label Password to label <NO-LABEL>}}
  return;
}
