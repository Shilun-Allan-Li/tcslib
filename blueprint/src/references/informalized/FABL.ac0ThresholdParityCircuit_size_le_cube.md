<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.ac0ThresholdParityCircuit_size_le_cube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Circuit Size Bound

**Claim.** For every natural number $m$, $m\,2^{2m}+2^m\le (2^m)^3$.

**Proof.** Use the elementary bound $m+1\le2^m$, together with $1\le2^m$. The latter gives $m2^m+1\le m2^m+2^m=(m+1)2^m$, and the former then gives $(m+1)2^m\le2^m\cdot2^m$. Since $2^{2m}=(2^m)^2$, multiplying the first inequality by $2^m$ identifies the left side of the desired bound with $(m2^m+1)2^m$. The preceding estimate bounds this by $(2^m\cdot2^m)2^m=(2^m)^3$.
