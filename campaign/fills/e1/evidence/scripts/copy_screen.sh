#!/usr/bin/env bash
# Copy screen (scripts/copy-text-screen-v3.py) over the five E1 files, plus the two pre-existing
# quantum files of ErrorCorrectingCodes for cross-file copies. Every pair it lists is classified in
# campaign/fills/e1/REPORT.md, § Duplication ledger.
set -u
cd "$(cd "$(dirname "$0")/../../../../.." && pwd)"
python3 -I scripts/copy-text-screen-v3.py . TCSlib/Quantum/Basic/Register.lean \
  TCSlib/Quantum/Basic/Gates.lean TCSlib/Quantum/Basic/ApplyOn.lean TCSlib/Quantum/Basic/Measure.lean \
  TCSlib/Quantum/Basic/Protocols.lean TCSlib/ErrorCorrectingCodes/QuantumHamming.lean \
  TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean
