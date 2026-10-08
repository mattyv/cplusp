#!/bin/sh
# A stand-in for Dafny that cannot parse the model, decision 0069. Dafny then stops before it verifies anything and prints no summary.
if [ "$1" = "--version" ]; then
  echo "4.11.0"
  exit 0
fi
for last in "$@"; do :; done
echo "$last(12,13): Error: this symbol not expected in VarDeclStatement"
echo "1 parse errors detected in model.dfy"
exit 2
