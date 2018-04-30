// RUN: %clang_analyze_cc1 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

int handle_request1(int N, CIFLabel("Secret") int (*Callback)(int))
{
  N *= 2;
  return Callback(N); // expected-warning{{Information flow violation to label <NO-LABEL> from label Secret}}
}

int handle_request2(CIFLabel("Secret") int N, int (*Callback)(int))
{
  N *= 2;
  return Callback(N); // expected-warning{{Information flow violation to label <NO-LABEL> from label Secret}}
}
