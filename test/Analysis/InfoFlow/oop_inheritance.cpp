// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

class CIFLabel("Base") Base {
public:
  CIFLabel("BaseF") int BM;
  Base() = default;
  Base(CIFLabel("BC") int a) {
  }
};

class CIFLabel("A") F : public Base {
  CIFLabel("F") int M;
public:
  F(CIFLabel("C") int a, float) {
      BM = a; // expected-warning{{Information flow violation from label C to label Base,BaseF}}
  }
  F(CIFLabel("C") int a) {
      M = a; // expected-warning{{Information flow violation from label C to label A,Base,F}}
  }
  // TODO: This shouldn't be allowed.
  F(CIFLabel("C") int a, unsigned) : Base(a) {
  }
  F() = default;
};


void foo() {
  CIFLabel("B") F f;
  F otherF = f; // expected-warning{{Information flow violation from label A,B,Base to label A,Base}}
  Base &base = f; // expected-warning{{Information flow violation from label A,B,Base to label Base}}
}
