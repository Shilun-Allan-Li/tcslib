<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.one_div_32768_sq_lt_claimInfo_of_distributionalError_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Information Lower Bound from Error

**Claim.** If a deterministic protocol’s distributional error is at most $1/32$, then its claim information is strictly greater than $(1/32768)^2$.

**Proof.** Assume for contradiction that the claim information is at most $(1/32768)^2$. Set $\gamma=1/64$; then $2\gamma^4/3=(1/32768)^2$, so the small-information hypothesis for the good-statistic probability bound holds. That bound gives $\frac14(1-4\gamma)=15/64$ as a lower bound on the measure of the good event. On the other hand, the good-event error bound says that this event’s measure times $\frac14-2\gamma=7/32$ is at most the protocol error. Combining these inequalities forces the error to be at least $(15/64)(7/32)$, which exceeds $1/32$. This contradicts the assumed error bound, proving the strict information lower bound.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.one_div_four_mul_one_sub_four_mul_le_measureReal_goodZEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.goodZEvent_mul_quarter_sub_two_mul_le_distributionalError`.
