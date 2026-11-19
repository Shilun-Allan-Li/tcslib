#!/usr/bin/env bash
# Duplication searches (gsw-6b-u18-u19), at the head working tree of /work/tcslib: pattern, scope,
# hit count, then the hits (path:line). grep -rnE over TCSlib/ and audits/ (TCSlib scope) and over
# .lake/packages/{mathlib,batteries}, and the Lean core sources of the toolchain (library scope).
cd /work/tcslib
CORE=$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init
s() { # scope pattern
  local scope=$1; shift; local pat="$*"; local dirs
  case $scope in
    tcslib) dirs="TCSlib audits" ;;
    lib) dirs=".lake/packages/mathlib/Mathlib .lake/packages/batteries/Batteries $CORE" ;;
  esac
  local hits; hits=$(grep -rnE --include=*.lean -- "$pat" $dirs 2>/dev/null)
  local n; n=$(printf '%s' "$hits" | grep -c . || true)
  echo "== [$scope] /$pat/ : $n hits"
  printf '%s\n' "$hits" | head -15 | cut -c1-220
}
s tcslib 'ofFamily_columns_le'
s tcslib '\.columns ≤'
s tcslib 'columns_le'
s tcslib 'dimensionBound\.eval [a-zκ]+ \+ 1\)'
s tcslib 'Nat\.clog 2 [^ ]+ ≤'
s lib 'theorem clog_le|lemma clog_le'
s lib 'clog [a-z] [a-z] ≤ [a-z]\b'
s tcslib '≤ bootNoise|le_bootNoise|bootNoise_pos|self_le_bootNoise'
s tcslib 'distAdv_nonneg|decisionAdvantage_nonneg|advantageAt_nonneg'
s tcslib 'theorem negligible_polyExpr_mul|Negligible\.polyExpr_mul'
s tcslib 'two_extractionError_le'
s tcslib 'distAdv_encrypt_le_of_width'
s tcslib 'lt_div_two|< [A-Za-z.()]+\.modulus / 2'
s tcslib 'singleBitSecure_of_dlweAssumption|indCPA_of_dlwe\b|leveledINDCPA_of_dlwe\b'
s tcslib 'negligible_collisions_of_SIS'
s tcslib 'two_mul_width_lt_of_ratio'
