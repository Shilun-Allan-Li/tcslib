<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.bounded_noise_qMoment_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Noise Moment Comparison

**Claim.** For a function bounded in absolute value by $1$, parameters $0\le\varepsilon\le1$ and $2+2\varepsilon\le q$ give the two stated bounds on the $q$-th power of its uniform $L^q$ norm after applying the indicated noise operators.

**Proof.** Set $r_1=1-\varepsilon$, $r_2=(1+2\varepsilon)^{-1/2}$, and $q_0=2+2\varepsilon$. The parameter assumptions imply $r_1,r_2\in[0,1]$ and $r_1/r_2\in[0,1]$; the last inequality uses $1-\varepsilon\le(1+2\varepsilon)^{-1/2}$ (`one_sub_le_inv_sqrt_one_add_two_mul`). Noise operators compose by multiplying their parameters (`noiseOperator_comp`), so applying the $L^q$ contraction bound for noise (`uniformLpNorm_noiseOperator_le`) with parameter $r_1/r_2$ to the already-smoothed function $T_{r_2}f$ gives $\|T_{r_1}f\|_q\le\|T_{r_2}f\|_q$. Raising both nonnegative sides to the positive power $q$ proves the first inequality. For the second, the bound $|T_{r_2}f(x)|\le1$ follows from preservation of the unit bound by noise (`abs_noiseOperator_le_one`). Since $q\ge q_0$, the pointwise powers satisfy $|T_{r_2}f(x)|^q\le |T_{r_2}f(x)|^{q_0}$, including when the value is zero. Averaging over the cube and using the moment formula for the uniform norm (`uniformLpNorm_rpow`) identifies this with $\|T_{r_2}f\|_{q_0}^{q_0}$. The two-to-$q_0$ hypercontractive estimate, with noise parameter $(q_0-1)^{-1/2}=r_2$, bounds this by $\|f\|_2^{q_0}$ (`twoQHypercontractivity`). Finally, $q_0=2(1+\varepsilon)$, so the latter is $(\|f\|_2^2)^{1+\varepsilon}$, as required.

**Key facts.** `FABL.one_sub_le_inv_sqrt_one_add_two_mul`, `FABL.uniformLpNorm_noiseOperator_le`, `FABL.noiseOperator_comp`, `FABL.abs_noiseOperator_le_one`, `FABL.uniformLpNorm_rpow`, `FABL.twoQHypercontractivity`.
