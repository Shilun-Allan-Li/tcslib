<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.positiveBias_bribeFunction_majority_head_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Bribery Majority Tail Identity

**Claim.** For nonnegative $k$ and positive $m$, setting the first $k$ coordinates of majority to $-1$ gives a positive bias equal to the average over all $m$-dimensional sign vectors of the indicator that their normalized sum exceeds $(k-1)/\sqrt m$.

**Proof.** First apply the bribed-majority bias identity (`positiveBias_bribeFunction_majority_head`) to express the positive bias as the average of the indicator that the remaining coordinates make the threshold positive. For each tail vector, the pointwise negative-bribe indicator identity (`majorityAfterHeadBribe_neg_one_one_indicator`) identifies this event with the upper-tail indicator at threshold $(k-1)/\sqrt m$. Since the indicators agree at every tail vector, their averages agree.

**Key facts.** `FABL.positiveBias_bribeFunction_majority_head`, `FABL.majorityAfterHeadBribe_neg_one_one_indicator`.
