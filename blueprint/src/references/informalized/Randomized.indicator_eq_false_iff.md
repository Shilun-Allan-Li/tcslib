<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.indicator_eq_false_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator detects nonmembership

**Claim.** For every language $V$ and bit string $y$, the Boolean indicator of $V$ at $y$ is false exactly when $y$ is not in $V$.

**Proof.** By definition the indicator is true when $y\in V$ and false otherwise. Thus its value is false precisely in the nonmembership case.
