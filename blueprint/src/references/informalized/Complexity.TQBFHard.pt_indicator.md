<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Language Indicator

**Claim.** If a language $L$ is decidable in logarithmic space, then its one-bit membership indicator is polynomial-time computable.

**Proof.** The logarithmic-space-to-polynomial-time inclusion (`Complexity.LOGSPACE_subset_P`) places $L$ in polynomial time. By the characterization of membership in $P$ (`Complexity.mem_P_iff`), there are a finite Turing machine and polynomial time bound that decide $L$. The same machine, time bound, and output behavior witness polynomial-time computability of the one-bit indicator of membership in $L$.

**Key facts.** `Complexity.LOGSPACE_subset_P`, `Complexity.mem_P_iff`.

**Caveat.** The supplied informal statement describes a composed encoding test, but the formal theorem and its proof establish only polynomial-time computability of the indicator of membership in $L.
