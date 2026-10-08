#!/bin/sh
# A stand-in for Dafny that always reports the time limit on c_slow, decision 0068. Z3 settles a hard contract at random under load,
# so a test of the time limit cannot rest on the real prover. The line is the one Dafny 4.11 prints. Line 7 is the header of c_slow
# in the model of model-prove-slow.cpp.
if [ "$1" = "--version" ]; then
  echo "4.11.0"
  exit 0
fi
for last in "$@"; do :; done
echo "$last(7,7): Error: Verification of 'c_slow' timed out after 1 seconds. (the limit can be increased using --verification-time-limit)"
echo
echo "Dafny program verifier finished with 5 verified, 0 errors, 1 time out"
exit 4
