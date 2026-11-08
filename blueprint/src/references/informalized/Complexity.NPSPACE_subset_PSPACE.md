<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean :: Complexity.NPSPACE_subset_PSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic Polynomial Space Lies in PSPACE

**Claim.** Every language decidable by a finite nondeterministic Turing machine using space bounded by a constant multiple of $n^c+1$ for some $c$ belongs to PSPACE.

**Proof.** A language in NPSPACE belongs to one of the classes $\mathrm{NSPACE}(n\mapsto n^k+1)$, by unpacking the defining union. For that exponent $k$, apply the polynomial-space inclusion theorem, which places every language in this fixed nondeterministic space class in PSPACE (`NSPACE_poly_subset_PSPACE`).

**Key facts.** `Complexity.NSPACE_poly_subset_PSPACE`.
