// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

CIFLabel("A") int foo();

CIFLabel("B") int foo() {
    return 3;
}

void test() {
  CIFLabel("X") int a = foo(); // expected-warning{{Information flow violation from label A,B,C to label X}}
}

CIFLabel("C") int foo();
