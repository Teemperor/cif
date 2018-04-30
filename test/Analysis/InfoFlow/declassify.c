// RUN: %clang_analyze_cc1 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

const char * crypt(const char *s);

void login(CIFLabel("Password") const char *Passwd) {
  const char *c = crypt(Passwd); // expected-warning{{Information flow violation from label Password to label <NO-LABEL>}}
}

void loginFixed(CIFLabel("Password") const char *Passwd) {
  const char *c = crypt(CIFDeclassify("Password->", Passwd));
}

void foo1(CIFLabel("Password") const char *Passwd) {
  CIFLabel("Public") const char *D = CIFDeclassify("Password->Public", Passwd);
}

void foo2(CIFLabel("Password") const char *Passwd) {
  CIFLabel("Public") const char *D = CIFDeclassify("Public->Public", Passwd); // expected-warning{{Information flow violation from label Password to label Public}}
}

void foo3(CIFLabel("Password") const char *Passwd) {
  CIFLabel("Public") const char *D = CIFDeclassify("->Public", Passwd); // expected-warning{{Information flow violation from label Password to label <NO-LABEL>}}
}

void foo4(const char *Passwd) {
  CIFLabel("Public") const char *D = CIFDeclassify("->Public", Passwd);
}
