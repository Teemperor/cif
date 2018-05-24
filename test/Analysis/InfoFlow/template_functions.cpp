// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

template<typename T>
bool equal(T &A, T &B) {
  return A == B;
}

bool GlobalB;

template<typename T>
void equalNonPure(T &A, T &B) {
  GlobalB = A == B;
}

CIFPureList {
  using ::equal;
}

void foo1() {
  int V1 = 1;
  CIFLabel("Secret") int V2 = 2;

  int B = equal(V1, V2);// expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
}

void foo2() {
  int V1 = 1;
  CIFLabel("Secret") int V2 = 2;

  equalNonPure(V1, V2); // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
}
