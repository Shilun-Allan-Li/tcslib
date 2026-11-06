#!/usr/bin/env bash
# Name-collision screen for the quantum-phase1 gate: the namespaces and namespaced declarations the
# gate introduces must not occur in any Lean file outside the audited ones.
set -u
cd "$(cd "$(dirname "$0")/../../../../.." && pwd)"
AUD='TCSlib/(Quantum|Complexity/Promise|Complexity/Counting)(/|\.lean)'
echo "Lean files in tree: $(find TCSlib -name '*.lean' | wc -l)"
echo "Namespaces Quantum / Counting / Promise / QuantumComplexity opened outside the audited files:"
hits="$(grep -rnE '^namespace (Quantum|Counting|Promise|QuantumComplexity)([. ]|$)' TCSlib \
  --include='*.lean' | grep -vE "$AUD")"
[ -n "$hits" ] && printf '%s\n' "$hits" || echo "  none"
echo "Declarations named Quantum.* / Counting.* / Promise.* outside the audited files:"
hits="$(grep -rnE '^(noncomputable |private |protected )*(def|theorem|lemma|abbrev|structure|inductive|class|instance) (Quantum|Counting|Promise)\.' \
  TCSlib --include='*.lean' | grep -vE "$AUD")"
[ -n "$hits" ] && printf '%s\n' "$hits" || echo "  none"
echo "Sanity: the same screen finds the audited namespaces inside the audited files:"
grep -rlE '^namespace (Quantum|Counting|Promise)([. ]|$)' TCSlib --include='*.lean' | grep -cE "$AUD"
