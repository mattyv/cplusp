#include <cfloat>

struct Reading {
  float value;  // BANNED
};

float half(float x) {  // BANNED
  return x * 0.5f;  // BANNED
}

double sum(double a, double b) {
  float s = static_cast<float>(a) + static_cast<float>(b);  // BANNED
  return s;  // BANNED
}

long double wide(double x) {  // BANNED
  return x;  // BANNED
}

double literal_sum() {
  return 16777216.0f + 1.0f;  // BANNED
}

double deduced_sum() {
  auto a = 16777216.0f;  // BANNED
  auto b = 1.0f;  // BANNED
  return a + b;  // BANNED
}
