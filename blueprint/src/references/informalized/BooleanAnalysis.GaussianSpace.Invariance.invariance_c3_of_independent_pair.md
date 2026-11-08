<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdOrder.lean :: BooleanAnalysis.GaussianSpace.Invariance.invariance_c3_of_independent_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third-Derivative Invariance Bound

**Claim.** Under the stated independence, hypercontractivity, centering, and unit second-moment assumptions, the difference between the two expectations of the smooth test function is bounded by the sum of the single-coordinate replacement costs, yielding the stated influence bound.

**Proof.** For each integer $r$ between $0$ and $n$, form a hybrid input that uses the left variables in the first $r$ coordinates and the right variables thereafter. The hybrid coordinates remain independent: each is selected from the original independent family through an injective index map (`hybridIndex_injective`). Consecutive hybrids differ only in coordinate $i$ (`hybridInput_succ_off`). Apply the single-coordinate replacement estimate (`single_coordinate_replacement_bound_c3`) to each consecutive pair, using the inherited hypercontractivity, centering, and second-moment hypotheses. This bounds the change in expectation at step $i$ by $(C/3)(1/\rho)^{3k}\mathrm{Inf}_i[F]^{3/2}$. The hybrid expectation bound (`hybrid_expectation_bound`) sums these changes to control the difference between the all-left and all-right expectations. Factoring out the common constant gives the claimed expression.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.hybridIndex_injective`, `BooleanAnalysis.GaussianSpace.Invariance.single_coordinate_replacement_bound_c3`, `BooleanAnalysis.GaussianSpace.Invariance.hybridInput_succ_off`, `BooleanAnalysis.GaussianSpace.Invariance.hybrid_expectation_bound`.
