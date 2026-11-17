<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.product_norm_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of the product moment norm

**Claim.** For $q>0$ and $a\ge0$, multiplying a function by $a$ multiplies its product moment norm by $a$.

**Proof.** The moment $\mathbb E_P[|f|^q]$ is nonnegative: each product mass is nonnegative and each power of an absolute value is nonnegative. Since $a\ge0$, $|af|=a|f|$, and the power rule for nonnegative factors gives $|af|^q=a^q|f|^q$. Taking expectation and pulling out the constant (`BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`) yields $\mathbb E_P[|af|^q]=a^q\mathbb E_P[|f|^q]$. Raising both sides to the power $1/q$ and using $q>0$ gives the asserted homogeneity, including $a=0$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`.
