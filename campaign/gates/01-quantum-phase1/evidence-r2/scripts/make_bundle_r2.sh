#!/usr/bin/env bash
# Assemble the quantum-phase1 round-2 audit bundle: the pack verbatim, then every attachment under a
# `## ===== <path> =====` header. Usage: make_bundle.sh <output.md>. The bundle is not committed
# (workflow.md §3); record its SHA-256 and section count in the resolutions file.
set -eu
cd "$(cd "$(dirname "$0")/../../../../.." && pwd)"
OUT="$1"; G=campaign/gates/01-quantum-phase1
files=(
  "$G/findings.md" "$G/resolutions.md" policy.md workflow.md campaign/design/plans/QuantumComplexityPlan.md
  TCSlib/Quantum.lean TCSlib/Quantum/Basic.lean
  TCSlib/Quantum/Basic/Register.lean TCSlib/Quantum/Basic/Gates.lean
  TCSlib/Quantum/Basic/ApplyOn.lean TCSlib/Quantum/Basic/Measure.lean
  TCSlib/Quantum/Basic/Protocols.lean
  TCSlib/Complexity/Promise.lean TCSlib/Complexity/Promise/Basic.lean
  TCSlib/Complexity/Counting.lean TCSlib/Complexity/Counting/PP.lean
  TCSlib/Complexity/Counting/GapP.lean TCSlib/Complexity/Counting/PolyTime.lean
  TCSlib/Complexity/Counting/Inclusions.lean
  TCSlib.lean
  TCSlib/Complexity/Randomized/Classes.lean TCSlib/Complexity/Randomized/PolyTimeModel.lean
  TCSlib/Complexity/ClassNP/NP.lean TCSlib/Complexity/ClassP/P.lean
)
for f in "$G"/evidence-r2/logs/* "$G"/evidence-r2/scripts/*; do files+=("$f"); done
{
  cat "$G/pack-r2.md"
  for f in "${files[@]}"; do
    printf '\n\n## ===== %s =====\n\n```\n' "$f"
    cat "$f"
    printf '\n```\n'
  done
} > "$OUT"
echo "bundle: $OUT"
echo "sections: $(grep -c '^## ===== ' "$OUT")"
echo "sha256: $(sha256sum "$OUT" | cut -d' ' -f1)"
echo "bytes: $(wc -c < "$OUT")"
