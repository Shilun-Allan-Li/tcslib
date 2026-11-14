#!/usr/bin/env bash
# Copy screen (scripts/copy-text-screen-v3.py) over the five E1 files plus the two pre-existing
# quantum files of ErrorCorrectingCodes. The screen opens a declaration only at
# def/theorem/lemma/abbrev/instance/structure/inductive, so an `example` would be read as part of
# the preceding declaration's body (E1 epoch audit, finding 7). The boundary check below lists
# every `example` in the screened files first; the screen's rows are exact only when it is empty.
set -u
cd "$(cd "$(dirname "$0")/../../../../.." && pwd)"
FILES=(TCSlib/Quantum/Basic/Register.lean TCSlib/Quantum/Basic/Gates.lean
  TCSlib/Quantum/Basic/ApplyOn.lean TCSlib/Quantum/Basic/Measure.lean
  TCSlib/Quantum/Basic/Protocols.lean TCSlib/ErrorCorrectingCodes/QuantumHamming.lean
  TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean)
echo "Boundary check: commands the screen does not open (example):"
grep -nE '^\s*(@\[[^]]*\]\s*)?example\b' "${FILES[@]}" || echo "  none"
echo
python3 -I scripts/copy-text-screen-v3.py . "${FILES[@]}"
