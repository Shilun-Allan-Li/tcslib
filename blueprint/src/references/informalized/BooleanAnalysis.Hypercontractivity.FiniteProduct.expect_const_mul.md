<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Scalar Multiple

**Claim.** For a real scalar $a$ and function $f$, the product expectation of $af$ equals $a$ times the product expectation of $f$.

**Proof.** Using the definition, the left-hand side is $\sum_x m(x)(a f(x))$. Associativity and commutativity of real multiplication put this in the form $a\sum_x m(x)f(x)$, which is $a\mathbb E_P f$.
