#!/bin/sh
# A stand-in for Dafny whose summary and exit status disagree, decision 0070.
if [ "$1" = "--version" ]; then
  echo "4.11.0"
  exit 0
fi
echo "Dafny program verifier finished with 3 verified, 1 error"
exit 0
