// Trusted: a sensor library returns a float, and a float converts to a double exactly. The conversion happens once, here at the
// edge. The gate refuses this file under the double_only row, which is the point. Verified code sees only the contract in example.cpp.
float raw_sensor();

double sensor_reading() {
  return static_cast<double>(raw_sensor());
}
