<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.positiveBias_bribeFunction_majority_head_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Bribery Majority Tail Identity

**Claim.** For nonnegative $k$ and positive $m$, setting the first $k$ coordinates of majority to $+1$ gives a positive bias equal to the average over all $m$-dimensional sign vectors of the indicator that their normalized sum exceeds $-(k+1)/\sqrt m$.

**Proof.** Use the bribed-majority bias identity (`positiveBias_bribeFunction_majority_head`) to rewrite the positive bias as the average of the indicator that the threshold after bribery is positive. The pointwise positive-bribe indicator identity (`majorityAfterHeadBribe_one_indicator`) shows that, for each tail vector, this indicator equals the upper-tail indicator at threshold $-(k+1)/\sqrt m$. Equality at every vector gives equality of the averages.

**Key facts.** `FABL.positiveBias_bribeFunction_majority_head`, `FABL.majorityAfterHeadBribe_one_indicator`.
