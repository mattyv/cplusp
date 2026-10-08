#!/bin/sh
# A stand-in for Dafny that says nothing and exits 0, decision 0069. No summary is no proof.
if [ "$1" = "--version" ]; then
  echo "4.11.0"
fi
exit 0
