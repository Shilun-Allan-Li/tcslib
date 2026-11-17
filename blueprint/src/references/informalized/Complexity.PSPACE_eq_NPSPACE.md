<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Savitch.lean :: Complexity.PSPACE_eq_NPSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic and nondeterministic polynomial space coincide

**Claim.** The class of languages decidable in polynomial space by deterministic finite Turing machines equals the class decidable in polynomial space by nondeterministic finite Turing machines.

**Proof.** The inclusion from deterministic to nondeterministic polynomial space is `Complexity.PSPACE_subset_NPSPACE`; the reverse inclusion is `Complexity.NPSPACE_subset_PSPACE`. The two inclusions give equality by antisymmetry of set inclusion.

**Key facts.** `Complexity.PSPACE_subset_NPSPACE`, `Complexity.NPSPACE_subset_PSPACE`.
