#!/bin/sh
# A stand-in for Dafny that always reports the time limit on c_slow, decision 0068. Z3 settles a hard contract at random under load,
# so a test of the time limit cannot rest on the real prover. The message is the one Dafny 4.11 prints, at the header of c_slow in the
# model of model-prove-slow.cpp. The stand-in finds that line, so a change to the prelude does not move it.
if [ "$1" = "--version" ]; then
  echo "4.11.0"
  exit 0
fi
for last in "$@"; do :; done
line=$(grep -n "^method c_slow" "$last" | cut -d: -f1)
echo "$last($line,7): Error: Verification of 'c_slow' timed out after 1 seconds. (the limit can be increased using --verification-time-limit)"
echo
echo "Dafny program verifier finished with 5 verified, 0 errors, 1 time out"
exit 4
