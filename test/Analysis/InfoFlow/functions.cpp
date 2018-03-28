// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

int strcmp(const char *username, const char *password);

#define CIFLabel(LBL) __attribute__((annotate("InfoFlow|" LBL)))

int login1(char *username, CIFLabel("Password") char *password) {
  int correct = strcmp(password, "letmein"); // expected-warning{{Information flow violation to label <NO-LABEL> from label Password}}

  return correct;
}

int login2(char *username, CIFLabel("Password") char *password) {
  CIFLabel("Password") int correct = strcmp(password, "letmein");
  return correct; // expected-warning{{Information flow violation to label <NO-LABEL> from label Password}}

}

CIFLabel("Password")
int login3(char *username, CIFLabel("Password") char *password) {
  CIFLabel("Password") int correct = strcmp(password, "letmein");
  return correct;
}
