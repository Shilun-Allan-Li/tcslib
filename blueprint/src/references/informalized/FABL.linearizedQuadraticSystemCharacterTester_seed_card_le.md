<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.linearizedQuadraticSystemCharacterTester_seed_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seed-Space Cardinality Bound

**Claim.** For every finite system $L$ of homogeneous quadratic equations in dimension $d$, the seed space of its linearized-system character tester has cardinality at most $2^{3d^2}$.

**Proof.** Split into whether the system has a solution. If it does, the tester uses the affine-character construction, whose seed space is a split-character seed. The bound for such seeds (`splitCharacterSeed_card_le_three_cube_powers`) gives cardinality at most $2^{3d}$. Since $d\le d^2$ for natural $d$ when $d\ge1$, this is at most $2^{3d^2}$; for $d=0$, the exponents agree. If the system has no solution, the tester uses a singleton seed space, whose cardinality is $1$, at most every power of $2$ with a natural exponent. These two cases establish the claimed bound.

**Key facts.** `FABL.splitCharacterSeed_card_le_three_cube_powers`.
