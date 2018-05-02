// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

struct OutputStream {
  void append(CIFLabel("Public") const char *C);
};

struct UserAccount {
  CIFLabel("Public") const char *UserName;
  CIFLabel("Public") const char *DisplayName;
  CIFLabel("Medical") const char *Treatment;
  CIFLabel("Password") const char *PasswordHash;
};

void createPublicInfo(UserAccount &A, OutputStream &S) {
  S.append("Welcome ");
  S.append(A.UserName);
  S.append("(");
  S.append(A.DisplayName);
  S.append(") ");
  S.append(A.Treatment); // expected-warning{{Information flow violation from label Medical to label Public}}

  // Printing the password to the output stream is not allowed.
  S.append(A.PasswordHash); // expected-warning{{Information flow violation from label Password to label Public}}
}

void createMedicalData(UserAccount &A, CIFLabel("Medical") OutputStream &S) {
  S.append("Welcome ");
  S.append(A.UserName);
  S.append("(");
  S.append(A.DisplayName);
  S.append(") ");
  S.append(A.Treatment);

  // Printing the password to the output stream is not allowed.
  S.append(A.PasswordHash); // expected-warning{{Information flow violation from label Password to label Medical,Public}}
}


void createLoginWelcome(UserAccount &A, OutputStream &S) {
  S.append("Welcome ");
  S.append(A.UserName);
  S.append("(");
  S.append(A.DisplayName);
  S.append(")");

  // Printing the password to the output stream is not allowed.
  S.append(A.PasswordHash); // expected-warning{{Information flow violation from label Password to label Public}}
}

void createUserAccount(CIFLabel("Public") const char *UserName,
                       CIFLabel("Password") const char *PasswordHash) {
  UserAccount A;
  A.UserName = PasswordHash; // expected-warning{{Information flow violation from label Password to label Public}}
  A.PasswordHash = PasswordHash;
}
