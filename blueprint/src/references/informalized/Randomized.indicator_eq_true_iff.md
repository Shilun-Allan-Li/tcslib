<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.indicator_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Indicator of Membership

**Claim.** For every language $V$ of bit strings and every bit string $y$, the Boolean indicator of $V$ at $y$ is true exactly when $y\in V$.

**Proof.** By definition, the indicator returns true when $y$ belongs to $V$ and false otherwise. Thus its value equals true if and only if $y\in V$.
