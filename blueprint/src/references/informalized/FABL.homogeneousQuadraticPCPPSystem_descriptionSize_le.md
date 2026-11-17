<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.homogeneousQuadraticPCPPSystem_descriptionSize_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Proof System Description Size Bound

**Claim.** For a positive dimension $d$, the associated homogeneous quadratic proof system has description size at most $5\cdot 2^{3(d+1)^2}$.

**Proof.** The description size is the number of seeds of the verifier. Because its verifier is a uniform mixture of three testers, its seed space is a disjoint union of their seed spaces, so its cardinality is the sum of the three seed cardinalities. The pair tester contributes at most $3\cdot 2^{3(d+1)^2}$ seeds; the system tester and the input-consistency tester contribute at most $2^{3(d+1)^2}$ each. Adding these bounds gives $5\cdot 2^{3(d+1)^2}$.

**Key facts.** `FABL.quadraticPairProofFunctionTester_seed_card_le`, `FABL.quadraticSystemProofFunctionTester_seed_card_le`, `FABL.quadraticInputConsistencyFunctionTester_seed_card_le`.
