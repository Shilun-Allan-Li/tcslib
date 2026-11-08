<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of Finite Sums

**Claim.** For a finite set $s$ and functions $F_i$, the expectation of their sum is the sum of their expectations: $\mathbb E_P[\sum_{i\in s}F_i]=\sum_{i\in s}\mathbb E_PF_i$.

**Proof.** Apply linearity of expectation for finite weighted sums (`expect_sum_mul`) with every coefficient equal to $1$. Each summand $1\cdot F_i$ reduces to $F_i$, and each weighted expectation $1\cdot\mathbb E_PF_i$ reduces to $\mathbb E_PF_i$, yielding the claimed identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum_mul`.
