<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Complexity.SPACE_eq_zero_of_exists_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collapse when a bound vanishes

**Claim.** If $s(n)=0$ for at least one natural number $n$, then $\mathrm{SPACE}(s)=\mathrm{SPACE}(0)$, where $0$ denotes the identically zero bound.

**Proof.** For the first inclusion, take a language in $\mathrm{SPACE}(s)$, witnessed by a constant $c$, a machine $M$, and a decision procedure whose space is bounded by $c s$. Since $s$ vanishes at some input length, so does this space bound. The zero-space rigidity lemma then implies that $M$ has no work tapes (Turing.FinTM.ComputesInSpace.k_eq_zero_of_exists_zero). With no work tapes, every computation of $M$ uses zero space; the witness already supplies a halting computation with the required output on each input. The lemma that a machine with no work tapes uses zero space (Turing.FinTM.computesInSpace_zero_of_k_eq_zero), followed by enlarging the bound from zero to the required zero bound, gives membership in $\mathrm{SPACE}(0)$. For the reverse inclusion, the identically zero function is pointwise at most $s$, so monotonicity of the space class (Complexity.SPACE.mono) gives $\mathrm{SPACE}(0)\subseteq\mathrm{SPACE}(s)$.

**Key facts.** `Turing.FinTM.ComputesInSpace.k_eq_zero_of_exists_zero`, `Turing.FinTM.computesInSpace_zero_of_k_eq_zero`, `Turing.FinTM.ComputesInSpace.mono`, `Complexity.SPACE.mono`.
