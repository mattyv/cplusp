#ifndef SECOND
void first(Base&) {
}
#else
void second(Base& b) {
  b.act();
}
#endif
