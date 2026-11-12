#!/usr/bin/env bash
# Assemble the quantum-e1 epoch audit bundle, round 2: the pack verbatim, then every attachment
# under a `## ===== <path> =====` header. Usage: make_bundle.sh <output.md>. Not committed
# (workflow.md §3).
set -eu
cd "$(cd "$(dirname "$0")/../../../.." && pwd)"
OUT="$1"; G=campaign/gates/02-quantum-e1; R="$G/evidence-r1"
files=(
  "$G/findings.md" "$G/resolutions.md" campaign/fills/e1/REPORT.md
  campaign/gates/01-quantum-phase1/resolutions.md policy.md workflow.md
  "$R/tcslib-r1-repairs.diff" "$R/tcslib-e1-r2.diff"
  TCSlib/Quantum/Basic/Register.lean TCSlib/Quantum/Basic/Gates.lean
  TCSlib/Quantum/Basic/ApplyOn.lean TCSlib/Quantum/Basic/Measure.lean
  TCSlib/Quantum/Basic/Protocols.lean
)
for f in "$R"/logs/* "$R"/scripts/*; do files+=("$f"); done
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
