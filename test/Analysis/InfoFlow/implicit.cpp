// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

int branch1(CIFLabel("S") int pass) {
  bool Result = false;
  if (pass == 1337) {
    Result = true; // expected-warning{{Information flow violation from label S to label <NO-LABEL>}}
  }
  return Result;
}

// Not branching on classified info
int branch2(int pass) {
  bool Result = false;
  if (pass == 1337) {
    Result = true;
  }
  return Result;
}

int branch3(CIFLabel("S") int pass) {
  if (pass == 1337) {
    return true; // expected-warning{{Information flow violation from label S to label <NO-LABEL>}}
  }
  return false; // expected-warning{{Information flow violation from label S to label <NO-LABEL>}}
}

int branch4(CIFLabel("S") int pass) {
  int Result;
  if (pass == 1337) {
    return true; // expected-warning{{Information flow violation from label S to label <NO-LABEL>}}
  }
  Result = false; // expected-warning{{Information flow violation from label S to label <NO-LABEL>}}
  return Result; // expected-warning{{Information flow violation from label S to label <NO-LABEL>}}
}

CIFLabel("S")
int branch4Fixed(CIFLabel("S") int pass) {
  CIFLabel("S") int Result;
  if (pass == 1337) {
    return true;
  }
  Result = false;
  return Result;
}
