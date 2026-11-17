<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean :: Complexity.PSPACE_subset_NPSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial space is contained in nondeterministic polynomial space

**Claim.** Every language decidable within a polynomial space bound by a deterministic finite Turing machine is also decidable within that bound by a nondeterministic finite Turing machine.

**Proof.** For each polynomial space bound $s(n)=n^c+1$, deterministic space bounded by $s$ is contained in nondeterministic space bounded by $s$ (`Complexity.SPACE_subset_NSPACE`). Applying this inclusion separately for each exponent $c$ and taking the unions that define $	extsf{PSPACE}$ and $	extsf{NPSPACE}$ gives the claimed containment.

**Key facts.** `Complexity.SPACE_subset_NSPACE`.
