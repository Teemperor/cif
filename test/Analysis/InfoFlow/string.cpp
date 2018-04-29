// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

class string {
};

string createUserAccount(CIFLabel("Public") string UserName,
                       CIFLabel("Password") string PasswordHash) {
  CIFLabel("Public") string Result = UserName;
  return Result; // expected-warning{{Information flow violation to label <NO-LABEL> from label Public}}
}

