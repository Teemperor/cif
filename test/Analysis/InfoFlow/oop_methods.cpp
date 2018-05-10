// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

class CIFLabel("A") NonPure {
public:
  int shouldBeA() {
    return 1;
  }
  CIFLabel("B") int shouldBeAB() {
    return 2;
  }
};

void foo() {
  NonPure P;
  int A = P.shouldBeA(); // expected-warning{{Information flow violation from label A to label <NO-LABEL>}}
  int AB = P.shouldBeAB(); // expected-warning{{Information flow violation from label A,B to label <NO-LABEL>}}
}

