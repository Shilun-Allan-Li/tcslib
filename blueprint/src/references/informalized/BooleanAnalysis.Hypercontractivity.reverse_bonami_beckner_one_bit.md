<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.reverse_bonami_beckner_one_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-bit reverse Bonami–Beckner inequality

**Claim.** For the stated parameters and every nonnegative function on the one-dimensional Boolean cube, $M_q(T_\rho f)\ge M_p(f)$.

**Proof.** If $f$ is identically zero, both means are zero, so the inequality holds. Otherwise, normalize the two values of $f$ as $c(1+a\,\mathrm{sign}(x))$, where $c>0$ and $-1\le a\le1$ (`normalize_one_bit`). For $|a|<1$, the normalized two-point inequality gives the result (`reverse_two_point_normalized`). The two sides of this inequality, as functions of $a$, are continuous: continuity of the power mean on positive exponents is provided by `continuous_lpMean_affine`, and the one-bit noise operator sends this affine function to the same form with coefficient $\rho a$ (`noiseOp_affine_one_bit`). The inequality therefore extends from the open interval $(-1,1)$ to its closure, including $a=\pm1$. Finally, scaling by $c$ scales each positive-order mean by $c$ (`lpMean_const_mul`), and preserves the inequality. In the zero-function case, the identification of the positive-order means with the usual power means is `lpMean_of_pos`.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.Hypercontractivity.normalize_one_bit`, `BooleanAnalysis.Hypercontractivity.continuous_lpMean_affine`, `BooleanAnalysis.Hypercontractivity.noiseOp_affine_one_bit`, `BooleanAnalysis.Hypercontractivity.reverse_two_point_normalized`, `BooleanAnalysis.Hypercontractivity.noiseOp_const_mul`, `BooleanAnalysis.Hypercontractivity.lpMean_const_mul`.
