// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

class CIFLabel("C") A {
public:
  void get(CIFLabel("O") CIFOut int &i) {
    i = 1;
  }
  void get2(CIFOut CIFLabel("O") int &i) {
    i = 1;
  }
};

void get1(CIFOut CIFLabel("O") int &i) {
  i = 1;
}

void get2(CIFOut int &i) {
  i = 1;
}

void foo() {
  A a;
  CIFLabel("I") int i;
  a.get(i); // expected-warning{{Information flow violation from label O to label I}}
  // Different order of attrs.
  a.get2(i); // expected-warning{{Information flow violation from label O to label I}}

  get1(i); // expected-warning{{Information flow violation from label O to label I}}
  get2(i);
}
