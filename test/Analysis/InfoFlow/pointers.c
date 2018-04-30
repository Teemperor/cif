// RUN: %clang_analyze_cc1 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

struct Str {
  const char *Data;
  int Len;
};

const char * crypt(const char *s);

void login(CIFLabel("Password") struct Str *Passwd) {
  const char *c = crypt(Passwd->Data);  // expected-warning{{Information flow violation to label <NO-LABEL> from label Password}}
}
