// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

class CIFLabel("B") F;

class CIFLabel("F") F {
};

void foo() {
  CIFLabel("A") F f;
  F otherF = f; // expected-warning{{Information flow violation from label A,B,C,F to label B,C,F}}
}

class CIFLabel("C") F;
