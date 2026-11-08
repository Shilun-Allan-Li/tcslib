<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_mem_PSPACE_of_ledger -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Space Membership

**Claim.** If a finite Turing machine decides a language with space at most $D(|x|+1)^f$ on every input, then the language belongs to polynomial space.

**Proof.** The hypothesis puts the language in $\mathrm{SPACE}(n\mapsto D(n+1)^f)$: use the given machine and absorb the time at which it halts into the witness for the space-class definition. The elementary estimate `succ_pow_le` gives $(n+1)^f\le 2^f(n^f+1)$, hence $D(n+1)^f\le(D2^f)(n^f+1)$. Monotonicity of the space class under a constant-factor bound (`Complexity.SPACE.mono_const`) therefore places the language in $\mathrm{SPACE}(n\mapsto n^f+1)$. By the defining inclusion of this polynomial space class in PSPACE (`Complexity.space_poly_subset_PSPACE`), the language belongs to PSPACE.

**Key facts.** `Complexity.SPACE.mono_const`, `Complexity.space_poly_subset_PSPACE`, `Complexity.succ_pow_le`.
