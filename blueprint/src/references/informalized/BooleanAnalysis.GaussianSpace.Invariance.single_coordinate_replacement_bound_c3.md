<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdOrder.lean :: BooleanAnalysis.GaussianSpace.Invariance.single_coordinate_replacement_bound_c3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-Coordinate Replacement Bound

**Claim.** Replacing one coordinate while keeping all other inputs fixed changes the expected value of a three-times continuously differentiable test function by at most $(C/3)(1/\rho)^{3k}\mathrm{Inf}_i[F]^{3/2}$.

**Proof.** Separate the polynomial evaluation into $A+D X_i$, where $A$ is the part independent of coordinate $i$ and $D$ is the evaluation of its coordinate derivative. Because the two input families agree off coordinate $i$, these two parts are the same for both families (`coordinate_parts_eq_of_off_coordinate`); the decomposition itself is given by the coordinate split (`eval_coordinate_split`). For either family, the corresponding coordinate is independent of $(A,D)$ (`indep_coordinate_parts`). The evaluations defining $A$ and $D$ are in $L^3$, since the input coordinates are in $L^3$ and the multilinear evaluation preserves that integrability (`evalMultilinearRV_memLp_nat`).

Apply the independent affine replacement estimate to compare the expectations of $\psi(A+D X_i)$ and $\psi(A+D Y_i$. Its bound is $(C/6)$ times the sum of the third absolute moments of the two coordinates, multiplied by the third absolute moment of $D$ (`independent_affine_replacement_bound_c3`). Independence factors each product moment: $\int|X_iD|^3=(\int|X_i|^3)(\int|D|^3)$, and likewise for $Y_i$ (`integral_abs_mul_pow`). The coordinate third-moment bound controls each product moment by $(1/\rho)^{3k}\mathrm{Inf}_i[F]^{3/2}$ (`coordinate_abs_third_moment`). Substituting these two bounds into the replacement estimate yields $(C/6)$ times twice that common bound, which is the claimed $(C/3)$ bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.coordinate_parts_eq_of_off_coordinate`, `BooleanAnalysis.GaussianSpace.Invariance.eval_coordinate_split`, `BooleanAnalysis.GaussianSpace.Invariance.indep_coordinate_parts`, `BooleanAnalysis.Hypercontractivity.evalMultilinearRV_memLp_nat`, `BooleanAnalysis.GaussianSpace.independent_affine_replacement_bound_c3`, `BooleanAnalysis.GaussianSpace.Invariance.integral_abs_mul_pow`, `BooleanAnalysis.GaussianSpace.Invariance.coordinate_abs_third_moment`, `BooleanAnalysis.GaussianSpace.integrable_test_of_memLp`.
