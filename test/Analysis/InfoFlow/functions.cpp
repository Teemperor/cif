// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

int strcmp(const char *username, const char *password);

#define secret(LBL) __attribute__((annotate("InfoFlow|" LBL)))

int login1(char *username, secret("Password") char *password) {
  int correct // expected-warning{{Information flow violation to label <NO-LABEL>}}
      = strcmp(password, "letmein"); // expected-note{{from label Password}}
  return correct;
}

int login2(char *username, secret("Password") char *password) {
  secret("Password") int correct = strcmp(password, "letmein");
  return  // expected-warning{{Information flow violation to label <NO-LABEL>}}
      correct; // expected-note{{from label Password}}
}

secret("Password")
int login3(char *username, secret("Password") char *password) {
  secret("Password") int correct = strcmp(password, "letmein");
  return correct;
}
