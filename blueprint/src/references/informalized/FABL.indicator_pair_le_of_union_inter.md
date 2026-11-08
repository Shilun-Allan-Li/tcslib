<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.indicator_pair_le_of_union_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator bound from union and intersection

**Claim.** If $P_+$ implies $A_+\vee A_-$ and $P_-$ implies $A_+\wedge A_-$, then the sum of the indicators for $P_+,P_-$ is at most the sum of the indicators for $A_+,A_-$ .

**Proof.** If neither $P_+$ nor $P_-$ holds, the left side is zero. If only $P_+$ holds, its implication guarantees that at least one of $A_+,A_-$ holds, so the right side is at least one. If only $P_-$ holds, both $A_+$ and $A_-$ hold, so the right side is two. If both propositions on the left hold, the implication from $P_-$ again guarantees that both $A_+$ and $A_-$ hold; both sides are then two. These cases establish the inequality.
