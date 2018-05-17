// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

class CIFLabel("F") F {
};

void foo() {
  CIFLabel("A") F f;
  F otherF = f; // expected-warning{{Information flow violation from label A,F to label F}}
}
