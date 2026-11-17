<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Replacement.lean :: BooleanAnalysis.GaussianSpace.single_coordinate_replacement_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-Coordinate Replacement Bound

**Claim.** Under the stated independence, moment, degree, and derivative hypotheses, replacing one input coordinate changes the expected test value by at most $\frac{C}{12}9^{k+1}\,\mathrm{Inf}_i[F]^2$.

**Proof.** Split the polynomial into its part independent of coordinate $i$ and its coordinate derivative. The off-coordinate agreement hypothesis ensures these two parts are the same functions of the other coordinates for $X$ and $Y$ (Invariance.coordinate_parts_eq_of_off_coordinate). The coordinate splitting identity then writes each evaluation as $A+D X_i$ or $A+D Y_i$, where $A$ is the coordinate-free part and $D$ is the coordinate derivative (Invariance.eval_coordinate_split). Independence of the inputs implies that each replaced coordinate is independent of the pair $(A,D)$ (Invariance.indep_coordinate_parts). The fourth-moment assumptions give the needed $L^4$ bounds on the polynomial evaluations, and hence integrability of the tested evaluations (Hypercontractivity.evalMultilinearRV_memLp; integrable_test_of_memLp_four). Apply the independent affine replacement estimate to bound the difference of expectations by $(3C/4)\int D^4\,d\mu$ (independent_affine_replacement_bound). Finally, the degree bound and invariance moment hypotheses bound this fourth moment by $9^k\,\mathrm{Inf}_i[F]^2$ (invariance_coordinate_fourth_moment). The resulting coefficient $(3C/4)9^k$ equals $(C/12)9^{k+1}$, giving the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.coordinate_parts_eq_of_off_coordinate`, `BooleanAnalysis.GaussianSpace.Invariance.eval_coordinate_split`, `BooleanAnalysis.GaussianSpace.Invariance.indep_coordinate_parts`, `BooleanAnalysis.Hypercontractivity.evalMultilinearRV_memLp`, `BooleanAnalysis.GaussianSpace.integrable_test_of_memLp_four`, `BooleanAnalysis.GaussianSpace.independent_affine_replacement_bound`, `BooleanAnalysis.GaussianSpace.invariance_coordinate_fourth_moment`.
