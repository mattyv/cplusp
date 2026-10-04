#include <cstdint>
#include <vector>

int32_t first_then_grow(std::vector<int32_t>& v) {
  const int32_t& r = v[0];  // BANNED
  v.push_back(1);
  return r;
}

int32_t last(std::vector<int32_t>& v) {
  int32_t& b = v.back();  // BANNED
  return b;
}

#include <map>

std::size_t read_count(std::map<int32_t, int32_t>& m, int32_t k) {
  int32_t v = m[k];  // BANNED
  return m.size() + static_cast<std::size_t>(v);
}

int32_t read(const int32_t* p);

int32_t first_by_pointer(std::vector<int32_t>& v) {
  return read(&v[0]);  // BANNED
}

#include <memory>

int32_t first_by_data(std::vector<int32_t>& v) {
  return read(v.data());  // BANNED
}

int32_t first_by_addressof(std::vector<int32_t>& v) {
  return read(std::addressof(v[0]));  // BANNED
}

#include <iterator>

int32_t first_by_std_data(std::vector<int32_t>& v) {
  return read(std::data(v));  // BANNED
}

int32_t first_by_ranges_data(std::vector<int32_t>& v) {
  return read(std::ranges::data(v));  // BANNED
}

int32_t first_by_to_address(std::vector<int32_t>& v) {
  return read(std::to_address(v.begin()));  // BANNED
}

int32_t grow_through_alias(std::vector<int32_t>& v) {
  std::vector<int32_t>& w = v;  // BANNED
  int32_t s = 0;
  for (const int32_t x : v) {
    s += x;
    w.push_back(x);
  }
  return s;
}

#include <functional>

int32_t grow_through_wrapper(std::vector<int32_t>& v) {
  std::reference_wrapper<std::vector<int32_t>> w(v);  // BANNED
  int32_t s = 0;
  for (const int32_t x : v) {
    s += x;
    w.get().push_back(x);
  }
  return s;
}

int32_t grow_through_ref(std::vector<int32_t>& v) {
  auto w = std::ref(v);  // BANNED
  w.get().push_back(1);
  return 0;
}
