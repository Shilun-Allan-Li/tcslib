<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.quadraticPairProofFunctionTester_seed_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seed Bound for the Proof Tester

**Claim.** For every d, the seed space of the Boolean-valued quadratic-pair proof tester has cardinality at most 3·2^{3(d+1)^2}.

**Proof.** The Boolean-valued proof tester has the same seed space as the quadratic-character pair tester, since Boolean conversion and domain reindexing leave the seeds unchanged. Its seed cardinality is therefore bounded by the established seed bound for the quadratic-character pair tester (quadraticCharacterPairTester_seed_card_le), which is 3·2^{3(d+1)^2}.

**Key facts.** `FABL.quadraticCharacterPairTester_seed_card_le`.
