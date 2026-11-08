<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of Finite Linear Combinations

**Claim.** For a finite set $s$, real coefficients $a_i$, and functions $F_i$, the expectation of their linear combination is $\mathbb E_P[\sum_{i\in s}a_iF_i]=\sum_{i\in s}a_i\mathbb E_PF_i$.

**Proof.** Expand expectation as a sum over outcomes, then distribute each outcome's mass across the finite sum over $i$. Interchanging the two finite sums groups the terms by $i$. Commutativity of real multiplication puts each resulting term in the form $a_i\sum_x m(x)F_i(x)$, which is $a_i\mathbb E_PF_i$.
