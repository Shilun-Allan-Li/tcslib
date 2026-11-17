<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.one_div_four_mul_one_sub_four_mul_le_measureReal_goodZEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Good Statistic

**Claim.** If $\gamma>0$ and the claim information is at most $2\gamma^4/3$, then the uniform hard-sample measure of the event that the statistic’s conditional special-bit-pair law is within total variation distance $2\gamma$ of uniform is at least $\frac14(1-4\gamma)$.

**Proof.** Let $A$ be the event that both special bits are zero. Its measure is $1/4$ (\texttt{measureReal_specialZeroZero}). Inside $A$, define the two bad slices where, respectively, Alice’s or Bob’s marginal distance from uniform exceeds $\gamma$. Each slice has measure at most $\gamma/2$, by the two bounds on bad slices under the information hypothesis (\texttt{measureReal_specialZeroZero_inter_xDistance_bad_le} and \texttt{measureReal_specialZeroZero_inter_yDistance_bad_le}). Every point of $A$ either lies in the good event or in one of these bad slices: if neither distance exceeds $\gamma$, both are at most $\gamma$, which implies goodness (\texttt{mem_goodZEvent_of_xDistance_yDistance_le}). Thus $A$ is covered by the good event and the two bad slices. Monotonicity and subadditivity of measure bound $1/4$ by the good-event measure plus the two bad-slice bounds, yielding the stated lower bound.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialZeroZero_inter_xDistance_bad_le`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialZeroZero_inter_yDistance_bad_le`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialZeroZero`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mem_goodZEvent_of_xDistance_yDistance_le`.
