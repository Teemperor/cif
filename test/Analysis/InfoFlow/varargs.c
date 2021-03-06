// RUN: %clang_analyze_cc1 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

void print(const char *, ...);

void login(CIFLabel("Password") const char *Passwd) {
  print("%s", Passwd);  // expected-warning{{Information flow violation from label Password to label <NO-LABEL>}}
}
