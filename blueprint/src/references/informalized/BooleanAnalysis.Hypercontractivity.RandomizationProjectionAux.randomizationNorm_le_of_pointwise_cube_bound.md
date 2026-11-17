<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.randomizationNorm_le_of_pointwise_cube_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrated randomization norm bound

**Claim.** If the uniform-cube power mean of the randomization of $f$ is bounded pointwise by $A$ times that of $g$, then the joint power mean over product outcomes and cube points obeys $\|Rf\|_q\le A\|Rg\|_q$.

**Proof.** For each function $h$, the inner cube moment $\mathbb E_r[|R_rh(x)|^q]$ is nonnegative, and so is its product expectation, since every product mass is nonnegative. Raise the assumed pointwise inequality between cube $q$-norms to the positive power $q$. The identity that the $q$th power of the cube norm is the cube moment (`cubeLpNorm_rpow`) converts this into $\mathbb E_r[|R_rf(x)|^q]\le A^q\mathbb E_r[|R_rg(x)|^q]$. Multiply by the nonnegative mass of $x$ and sum over outcomes. Taking the power $1/q$, which preserves order because $q>0$, bounds the joint moment for $f$ by the corresponding moment for $g$ with factor $A^q$. The factor pulls out of the product expectation by constant scaling (`expect_const_mul`); its $1/q$ power is $A$, using $A\ge0$ and the real-power multiplication law. These steps give the desired joint norm inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.cubeLpNorm_rpow`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`, `BooleanAnalysis.Hypercontractivity.expect_rpow_abs_nonneg`.
