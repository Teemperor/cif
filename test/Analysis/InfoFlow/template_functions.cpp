// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

template<typename T>
void equal(T &A, T &B) {
  bool Result = A == B;
  (void)Result;
}

template<typename T>
void equalNonPure(T &A, T &B) {
  bool Result = A == B;
  (void)Result;
}

CIFPure {
  using ::equal;
}

void foo1() {
  int V1 = 1;
  CIFLabel("Secret") int V2 = 2;

  equal(V1, V2);// expected-warning{{Information flow violation to label <NO-LABEL> from label Secret}}
}

void foo2() {
  int V1 = 1;
  CIFLabel("Secret") int V2 = 2;

  equalNonPure(V1, V2); // expected-warning{{Information flow violation to label <NO-LABEL> from label Secret}}
}
