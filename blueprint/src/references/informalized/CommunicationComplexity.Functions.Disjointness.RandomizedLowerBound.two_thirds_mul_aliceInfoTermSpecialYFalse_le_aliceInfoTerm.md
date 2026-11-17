<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.two_thirds_mul_aliceInfoTermSpecialYFalse_le_aliceInfoTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Information on the False Special-Bit Branch

**Claim.** Under the distribution conditioned on disjoint inputs, two-thirds times the conditional mutual information on the branch where Bob’s special bit is false is at most the conditional mutual information under the full disjointness-conditioned distribution.

**Proof.** Let $\mu$ be the disjointness-conditioned probability measure and let $A$ be the event that Bob’s special bit is false. First, this branch has measure $2/3$ under $\mu$ ( `disjointCondMeasure_measureReal_specialY_false` ). Next, $A$ is determined by the conditioning variable $(T,X_{<T},Y_{\geq T})$: it is the preimage of the set of conditioning values whose $Y_{\geq T}$ component has false bit at $T$ ( `specialY_false_eq_preimage_aliceClaimConditioningYFalseValues` ). The event-preimage inequality for conditional mutual information says that the probability of any branch determined by the conditioning variable, multiplied by the conditional mutual information within that branch, is at most the unconditional conditional mutual information ( `measureReal_mul_cond_condMutualInfo_le_condMutualInfo_of_event_eq_preimage` ). Apply it to $A$, with the special bit as the first variable, the transcript as the second, and $(T,X_{<T},Y_{\geq T})$ as the conditioning variable. Substituting the branch probability $2/3$ and the definitions of the two information terms yields the desired inequality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialY_false`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialY_false_eq_preimage_aliceClaimConditioningYFalseValues`, `ProbabilityTheory.measureReal_mul_cond_condMutualInfo_le_condMutualInfo_of_event_eq_preimage`.
