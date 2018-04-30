// RUN: %clang_analyze_cc1 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

struct Str {
  const char *Data;
  int Len;
};

struct LoginInfo {
  CIFLabel("Password") struct Str *Passwd;
};

const char * crypt(const char *s);

void login(CIFLabel("Password") struct Str *Passwd) {
  const char *c = crypt(Passwd->Data);  // expected-warning{{Information flow violation to label <NO-LABEL> from label Password}}
}

void login2(struct LoginInfo *L) {
  const char *c = crypt(L->Passwd->Data);  // expected-warning{{Information flow violation to label <NO-LABEL> from label Password}}
}

void setLogin(struct LoginInfo *L, CIFLabel("Password") const char* NewPasswd) {
  L->Passwd->Data = NewPasswd;
}
