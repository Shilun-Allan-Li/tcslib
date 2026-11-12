#!/usr/bin/env bash
# where.sh name... : definitions and use counts across TCSlib/ and audits/
cd /workspace/dlc
for n in "$@"; do
  echo "## $n"
  grep -rnE "^(private |protected |noncomputable |@\[[^]]*\] )*(theorem|lemma|def|abbrev) ([A-Za-z_.]*\.)?$n\b" --include=*.lean TCSlib audits 2>/dev/null | cut -c1-200
  echo "  uses: $(grep -rlw "$n" --include=*.lean TCSlib audits 2>/dev/null | tr '\n' ' ')"
done
