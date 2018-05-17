// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

int foo(CIFLabel("A") int i);

int foo(CIFLabel("B") int i) {
    return 3;
}

void test() {
  CIFLabel("X") int a = 0;
  foo(a); // expected-warning{{Information flow violation from label X to label A,B,C}}
}

int foo(CIFLabel("C") int i);
