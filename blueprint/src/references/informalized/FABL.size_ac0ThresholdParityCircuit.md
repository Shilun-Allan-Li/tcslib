<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.size_ac0ThresholdParityCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Circuit Size Bound

**Claim.** For every $m\ge7$, the constructed circuit has size at most $m2^{2m}+2^m$.

**Proof.** The circuit size is the length of its first layer plus the number of internal nodes in its tail. Removing the cast that aligns the tail's input type does not change its internal-node count (`circuitTail_internalNodeCount_cast`). The first layer has size $m2^{2m}$, while the middle layer has $2^{m-1}$ gates (`length_blockFirstLayer`, `length_blockMiddleLayer`); the output layer contributes no internal nodes. Since $2^{m-1}\le2^m$, their sum is at most $m2^{2m}+2^m$.

**Key facts.** `FABL.circuitTail_internalNodeCount_cast`, `FABL.length_blockFirstLayer`, `FABL.length_blockMiddleLayer`.
