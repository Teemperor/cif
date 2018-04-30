// RUN: %clang_analyze_cc1 -std=c++11 -analyzer-checker=security.SecureInformationFlow -verify %s

#include "CIF.h"

template<typename T>
class vector {
public:
  T front() {
    return T();
  }

  void push_back(T t) {
    (void)t;
  }
};

void send(CIFLabel("Secret") int Ciphertext);

void crypt1(CIFLabel("Secret") vector<int> Primes, int Msg) {
  int P = Primes.front(); // expected-warning{{Information flow violation from label Secret to label <NO-LABEL>}}
  CIFLabel("Secret") int Ciphertext = Msg * P;
  send(Ciphertext);
}

void crypt2(CIFLabel("Secret") vector<int> Primes, int Msg) {
  CIFLabel("Secret") int P = Primes.front();
  CIFLabel("Secret") int Ciphertext = Msg * P;
  send(Ciphertext);
}


void store1(CIFLabel("Secret") vector<int> Primes, CIFLabel("Public") int NewPrime) {
  Primes.push_back(NewPrime); // expected-warning{{Information flow violation from label Public to label Secret}}
}
