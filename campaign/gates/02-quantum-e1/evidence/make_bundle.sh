#!/usr/bin/env bash
# Assemble the quantum-e1 epoch audit bundle: the pack verbatim, then every attachment under a
# `## ===== <path> =====` header. Usage: make_bundle.sh <output.md>. Not committed (workflow.md §3).
set -eu
cd "$(cd "$(dirname "$0")/../../../.." && pwd)"
OUT="$1"; G=campaign/gates/02-quantum-e1; F=campaign/fills/e1
files=(
  "$F/REPORT.md" campaign/gates/01-quantum-phase1/resolutions.md policy.md workflow.md
  "$G/evidence/tcslib-e1.diff"
  TCSlib/Quantum/Basic/Register.lean TCSlib/Quantum/Basic/Gates.lean
  TCSlib/Quantum/Basic/ApplyOn.lean TCSlib/Quantum/Basic/Measure.lean
  TCSlib/Quantum/Basic/Protocols.lean
)
for f in "$F"/evidence/logs/* "$F"/evidence/scripts/*; do files+=("$f"); done
{
  cat "$G/pack.md"
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
