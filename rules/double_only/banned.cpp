#include <cfloat>

struct Reading {
  float value;  // BANNED
};

float half(float x) {  // BANNED
  return x * 0.5f;
}

double sum(double a, double b) {
  float s = static_cast<float>(a) + static_cast<float>(b);  // BANNED
  return s;
}

long double wide(double x) {  // BANNED
  return x;
}
