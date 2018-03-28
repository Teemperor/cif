// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#define secret(LBL) __attribute__((annotate("InfoFlow|" LBL)))

struct OutputStream {
  void append(secret("Public") const char *C);
};

struct UserAccount {
  secret("Public") const char * UserName;
  secret("Password") const char * PasswordHash;
};

void createRequest(UserAccount &A, OutputStream &S) {
  S.append(A.UserName);
  S.append(A.PasswordHash); // expected-warning{{Information flow violation to label Public from label Password}}
}

void createUserAccount(secret("Public") const char *UserName,
                       secret("Password") const char *PasswordHash) {
  UserAccount A;
  A.UserName = PasswordHash; // expected-warning{{Information flow violation to label Public from label Password}}
  A.PasswordHash = PasswordHash;
}

