<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.SAT_NPHard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# SAT is NP-hard

**Claim.** Every language in NP has a polynomial-time many-one reduction to SAT.

**Proof.** Take any language $L$ in NP. The Cook–Levin reduction fact `clA5Reduction` supplies a polynomial-time many-one reduction from $L$ to SAT. Since this applies to every such $L$, SAT is NP-hard.

**Key facts.** `Complexity.clA5Reduction`.
