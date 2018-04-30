// RUN: %clang_analyze_cc1 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

void foo() {
  CIFLabel("Secret") int Secret = 123;
  int Normal = 0;
  Normal = Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  Normal *= Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  Normal /= Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  Normal %= Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  Normal -= Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  Normal += Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  Normal &= Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  Normal ^= Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  Normal |= Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  Normal <<= Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  Normal >>= Secret; // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
}
