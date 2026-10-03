struct Flags {
  unsigned readable : 1 = 0;  // BANNED
  unsigned writable : 1 = 0;  // BANNED
  unsigned reserved : 6 = 0;  // BANNED
};

bool can_write(const Flags& f) {
  return f.writable != 0;
}
