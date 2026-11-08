<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.RP_PTMWith_error_reduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Sided Error Reduction

**Claim.** For any natural numbers $c,d$, a language decidable in polynomial time with one-sided acceptance probability at least $\min(2/3,(n+1)^{-c})$ on members can also be decided in polynomial time with one-sided acceptance probability at least $1-2^{-((n+1)^d+1)}$.

**Proof.** Fix a language in the source class. Its membership characterization gives a polynomial-time machine satisfying the weak one-sided acceptance threshold (Randomized.mem_RP_PTMWith_iff). Apply the polynomial-time one-sided error-reduction theorem: it upgrades this weak threshold to the stated strong threshold while preserving polynomial-time decidability (Randomized.rp_error_reduction_polyTime). The target membership characterization then places the language in the desired class (Randomized.mem_RP_PTMWith_iff).

**Key facts.** `Randomized.mem_RP_PTMWith_iff`, `Randomized.rp_error_reduction_polyTime`, `Randomized.mem_RP_PTMWith_iff`.
