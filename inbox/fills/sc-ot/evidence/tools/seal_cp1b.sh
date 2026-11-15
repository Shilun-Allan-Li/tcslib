#!/usr/bin/env bash
cd /workspace/scot
EV=/workspace/exchange/inbox/fills/sc-ot/evidence/seal-cp1
F="TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Shape.lean TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean"
python3 -I /workspace/scot-tools/seal_run.py /workspace/scot cp1Bs $EV/seal-Bs.jsonl TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean
python3 -I /workspace/scot-tools/seal_run.py /workspace/scot cp1Bc $EV/seal-Bc.jsonl --coe-open $F
echo SEAL-CP1-DONE
