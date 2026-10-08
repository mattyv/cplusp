#!/bin/sh
# A stand-in for Dafny whose summary reports an error that it gives no line for, decision 0070. That is a fault of the tool, not a proof.
if [ "$1" = "--version" ]; then
  echo "4.11.0"
  exit 0
fi
echo "Dafny program verifier finished with 0 verified, 1 error"
exit 4
