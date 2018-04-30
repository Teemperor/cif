// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

class string {
  string operator+(const string& S);
};

string createUserAccount1(CIFLabel("Public") string UserName,
                       CIFLabel("Password") string PasswordHash) {
  string Result = UserName; // expected-warning{{Information flow violation from label Public to label <NO-LABEL>}}
  return Result;
}


string createUserAccount2(CIFLabel("Public") string UserName,
                       CIFLabel("Password") string PasswordHash) {
  CIFLabel("Public") string Result = UserName;
  return Result; // expected-warning{{Information flow violation from label Public to label <NO-LABEL>}}
}

