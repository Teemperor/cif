// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

class CIFLabel("A") F  {
  CIFLabel("F") int M = 0;
  int MB = M; // expected-warning{{Information flow violation from label A,F to label A}}
public:
  F(int a) : M(a) {
  }
  F(CIFLabel("C") int a, double) : M(a) { // expected-warning{{Information flow violation from label C to label A,F}}
  }
};
