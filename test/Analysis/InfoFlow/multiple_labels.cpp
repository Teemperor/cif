// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

struct SecureOutputStream {
  void append(CIFLabel("Public,Password") const char *C);
};

struct UserAccount {
  CIFLabel("Public") const char *UserName;
  CIFLabel("Public") const char *DisplayName;
  CIFLabel("Password") const char *PasswordHash;

  CIFLabel("Public,Password") const char *getLogData() const;
};

void createPublicInfo(UserAccount &A, SecureOutputStream &S) {
  S.append("Welcome ");
  S.append(A.UserName);
  S.append("(");
  S.append(A.DisplayName);
  S.append(")");

  S.append("PasswordHash: ");
  // Printing the password to the output stream is not allowed.
  S.append(A.PasswordHash);
}

void logInfo1(UserAccount &A, SecureOutputStream &S) {
  CIFLabel("Public,UnusedLabel") const char *D;
  D = A.getLogData(); // expected-warning{{Information flow violation from label Password,Public to label Public,UnusedLabel}}
  S.append(D); // expected-warning{{Information flow violation from label Public,UnusedLabel to label Password,Public}}
}

void logInfo2(UserAccount &A, SecureOutputStream &S) {
  CIFLabel("Public") const char *D;
  D = A.getLogData(); // expected-warning{{Information flow violation from label Password,Public to label Public}}
  S.append(D);
}
