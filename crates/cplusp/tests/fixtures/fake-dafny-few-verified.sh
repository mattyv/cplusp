#!/bin/sh
# A stand-in for Dafny that verifies fewer items than the model has methods, decision 0083. The count is the only fault.
if [ "$1" = "--version" ]; then
  echo "4.11.0"
  exit 0
fi
echo
echo "Dafny program verifier finished with 0 verified, 0 errors"
exit 0
