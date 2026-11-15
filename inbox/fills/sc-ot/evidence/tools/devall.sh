#!/usr/bin/env bash
for m in Shape Efficiency Simulators ViewA Predictor ViewB; do /workspace/scot-tools/dev.sh TCSlib/Cryptography/SecureComputation/ObliviousTransfer/$m 20 || true; done
/workspace/scot-tools/dev.sh TCSlib/Cryptography/SecureComputation/ObliviousTransfer 20
echo DEVALL-DONE
