<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.xor_vec_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero vector is an XOR identity

**Claim.** For every $x\in\{0,1\}^n$, componentwise XOR with the all-zero vector satisfies $x\oplus\mathbf{0}=x$.

**Proof.** At each coordinate $i$, the left side has value $x_i\oplus 0$. XOR with false leaves a Boolean unchanged, so the coordinate equals $x_i$. Equality at every coordinate gives the claimed vector identity.
