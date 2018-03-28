// RUN: %clang_analyze_cc1 -analyzer-checker=security.SecureInformationFlow -verify %s

int strcmp(const char *username, const char *password);

#define secret(LBL) __attribute__((annotate("InfoFlow|" LBL)))

int login(char *username, secret("Password") char *password) {
  int correct // expected-warning{{Information flow violation to label <NO-LABEL>}}
      = strcmp(password, "letmein"); // expected-note{{from label Password}}
  return correct;
}
