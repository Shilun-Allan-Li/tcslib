<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.reverse_minkowski_mixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mixed power-mean comparison

**Claim.** For $0<q\le p$ and nonnegative $F$ on the product of the $n$-cube and the one-dimensional cube, $M_q(x\mapsto M_p(y\mapsto F(x,y)))\ge M_p(y\mapsto M_q(x\mapsto F(x,y)))$.

**Proof.** Let $r=p/q\ge1$, so $p>0$. The positive-exponent formula for the extended means rewrites the claimed inequality in terms of expectations of powers. After raising both sides to the positive power $p$, and using monotonicity of positive real powers, it suffices to compare the corresponding unweighted finite sums. Apply the finite-sum Minkowski inequality in exponent $r$ to the nonnegative array $a(x,y)=F(x,y)^q$ (`finset_Lr_sum_le`). It states that the $r$-norm over $y$ of the sums over $x$ is at most the sum over $x$ of the $r$-norms over $y$. Rewriting $a(x,y)^r=F(x,y)^p$ gives exactly the required comparison of the inner power means. The factors from the uniform measures are nonnegative and separate from these sums, so restoring them preserves the inequality and yields the stated normalized means.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.expect_eq_fintypeExpect`, `BooleanAnalysis.Hypercontractivity.finset_Lr_sum_le`.
