<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Hoeffding.lean :: mul_one_sub_le_quarter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fraction times its complement

**Claim.** If $0\le x\le1$, then $x(1-x)\le1/4$.

**Proof.** The square $(x-\tfrac12)^2$ is nonnegative. Expanding this inequality gives $x^2-x+\tfrac14\ge0$, equivalently $x(1-x)\le\tfrac14$.
