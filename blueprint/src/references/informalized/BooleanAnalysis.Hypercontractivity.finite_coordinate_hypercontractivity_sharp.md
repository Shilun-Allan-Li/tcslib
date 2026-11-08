<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.finite_coordinate_hypercontractivity_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp Finite-Coordinate Hypercontractivity

**Claim.** For normalized finite weights bounded below by $\lambda$, and the stated parameters, the weighted $q$-norm of the noisy function is at most its weighted $2$-norm, and its weighted $2$-norm is at most its weighted $q/(q-1)$-norm.

**Proof.** First note that every weight is nonnegative. The proof establishes a common quadratic moment bound: monotonicity in the noise radius compares $\rho$ with the sharp radius, and the sharp discrete contraction theorem bounds the resulting quadratic expression by the $q/(q-1)$ moment (\texttt{finite\_noise\_quadratic\_mono}, \texttt{SharpDiscrete.finite\_noise\_sharp\_contraction}).

For the first asserted norm inequality, apply finite-noise duality to that quadratic bound; it yields the squared-moment comparison between the noisy $q$-moment and the input second moment (\texttt{SharpDiscrete.finite\_noise\_duality}). For the second, the quadratic identity for the noisy second moment identifies it with the same quadratic expression, which is bounded by the sharp contraction estimate (\texttt{SharpDiscrete.finite\_noise\_identities}). In each case all moments are nonnegative because the weights and absolute-value powers are nonnegative. Taking the corresponding positive power roots converts the squared-moment inequalities into the stated norm inequalities (\texttt{rpow\_norm\_le\_of\_sq\_moments}).

**Key facts.** `BooleanAnalysis.Hypercontractivity.finite_noise_quadratic_mono`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_sharp_contraction`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_duality`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_identities`, `BooleanAnalysis.Hypercontractivity.rpow_norm_le_of_sq_moments`.
