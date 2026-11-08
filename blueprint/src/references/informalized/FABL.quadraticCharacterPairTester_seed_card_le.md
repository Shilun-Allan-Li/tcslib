<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.quadraticCharacterPairTester_seed_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tester Seed-Count Bound

**Claim.** For every natural number $d$, the seed space of the quadratic character pair tester has cardinality at most $3\cdot2^{3(d+1)^2}$.

**Proof.** The tester is a uniform mixture of three component testers, so its seed space is a dependent sum over the three mixture choices, with each fiber the seed space of the corresponding component. The cardinality of a finite dependent sum is the sum of the fiber cardinalities. Each component seed is a product of binary cubes: the first two components use two cubes of dimension $d$ or $d^2$, and the third uses two cubes of dimension $d$ together with one cube of dimension $d^2$. A binary cube of dimension $m$ has $2^m$ elements, and product cardinalities multiply. Thus the component seed counts are respectively $2^{2d}$, $2^{2d^2}$, and $2^{2d+d^2}$. Each is at most $2^{3(d+1)^2}$, so summing the three bounds gives the result.
