// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

class CIFLabel("A") Foo {
  CIFLabel("S") int pass = 0;
  int otherMember = 0;
public:
  bool branch1() {
    if (pass == 1337) {
      return true; // expected-warning{{Information flow violation from label A,S to label A}}
    }
    return false; // expected-warning{{Information flow violation from label A,S to label A}}
  }
  CIFLabel("S") bool branch1Fixed() {
    if (pass == 1337) {
      return true;
    }
    return false;
  }
  bool branch2() {
    if (pass == 1337) {
      otherMember = pass; // expected-warning{{Information flow violation from label A,S to label A}}
    }
    return true;
  }

};

