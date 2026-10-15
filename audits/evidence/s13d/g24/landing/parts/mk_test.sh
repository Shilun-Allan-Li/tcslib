#!/usr/bin/env bash
# Assemble a test file: imports given in $2 (comma separated), bodies $3...; output $1.
out="$1"; imps="$2"; shift 2
{ for m in ${imps//,/ }; do echo "import $m"; done
  printf '\nset_option maxHeartbeats 0\nset_option relaxedAutoImplicit false\nset_option autoImplicit false\n\n'
  for b in "$@"; do cat "$b"; echo; done; } > "$out"
