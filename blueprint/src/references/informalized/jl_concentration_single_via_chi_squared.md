<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/ConcentrationBound.lean :: jl_concentration_single_via_chi_squared -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Single-Vector Concentration

**Claim.** For a random matrix with independent Gaussian entries of variance $1/k$, the squared norm of the image of any fixed vector deviates from its squared norm by more than an $\varepsilon$-fraction with probability at most $2\exp(-k\varepsilon^2/8)$.

**Proof.** First handle $x=0$: its image is zero, so the bad event is empty and the bound follows from the probability bound for zero vectors (`concentration_zero`). Now suppose $x\ne0$. For each row define $Y_i=(Ax)_i$. Measurability follows by expressing the row projection as a finite sum of measurable matrix entries times fixed coordinates. The weighted-sum law for independent Gaussians (`sum_scaled_iid_gaussian_map`) shows that each $Y_i$ has law $N(0,\|x\|^2/k)$: the row entries have variance $1/k$, and $\sum_jx_j^2=\|x\|^2$. Independence of the row projections follows from independence of the rows (`rows_indep`). Normalize by setting $Z_i=Y_i/\|x\|$. The scaling law for a Gaussian (`map_const_mul_gaussian`) gives $Z_i\sim N(0,1/k)$, and applying the same coordinatewise scaling preserves independence. Since $Y_i=\|x\|Z_i$, summing squares yields $\sum_iY_i^2=\|x\|^2\sum_iZ_i^2$. Using the Euclidean norm identity (`norm_sq_toEuclideanLin`), this rewrites the original bad event as $\{\varepsilon<|\sum_iZ_i^2-1|\}$. The chi-squared tail bound (`chi_squared_tail`) for independent $N(0,1/k)$ variables now gives the claimed probability.

**Key facts.** `concentration_zero`, `toEuclideanLin_apply_eq_sum`, `sum_scaled_iid_gaussian_map`, `rows_indep`, `map_const_mul_gaussian`, `norm_sq_toEuclideanLin`, `chi_squared_tail`.
