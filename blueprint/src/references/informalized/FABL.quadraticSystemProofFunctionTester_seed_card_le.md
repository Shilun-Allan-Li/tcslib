<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.quadraticSystemProofFunctionTester_seed_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seed-Space Cardinality Bound

**Claim.** For every natural number $d$ and every list $L$ of homogeneous quadratic equations in $d$ variables over $\mathbb F_2$, the seed space of the associated quadratic-system proof tester has cardinality at most $2^{3(d+1)^2}$.

**Proof.** The proof tester’s seed space is the same as that of its underlying linearized-system character tester, since the outer construction only pads queries, changes the answer alphabet, and reindexes the domain. The latter seed space has cardinality at most $2^{3d^2}$ (`linearizedQuadraticSystemCharacterTester_seed_card_le`). Since $d^2\leq(d+1)^2$ and the exponent is nonnegative, monotonicity of natural-number exponentiation gives $2^{3d^2}\leq 2^{3(d+1)^2}$. Combining these inequalities proves the claimed bound.

**Key facts.** `FABL.linearizedQuadraticSystemCharacterTester_seed_card_le`.
