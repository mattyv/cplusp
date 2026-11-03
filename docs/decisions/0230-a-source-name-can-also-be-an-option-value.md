# 0230: A source name can also be an option value

The gate removes the compiler and the source input from each compilation
database entry. It must keep an option value that names the same source.
For example, `-MT main.cpp -c main.cpp` must retain `-MT main.cpp`.

The driver consumes an option and its value together. It uses the core's
existing list of options that take a value. The function that reads this list
is now public. Its implementation and proof contract do not change.

The regression test uses both `-MT` and `-MQ`. It puts the source input before
and after the option. The option value uses a relative path with `..` that
resolves to the source. Each run must pass the gate.

The list of options is still the one described by decisions 0130 and 0135.
This change does not add support for unknown compiler options.
