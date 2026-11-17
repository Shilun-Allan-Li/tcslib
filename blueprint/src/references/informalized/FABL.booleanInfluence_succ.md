<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityOptimality.lean :: FABL.booleanInfluence_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Under Coordinate Restriction

**Claim.** For a coordinate among the last $n$ coordinates of the $(n+1)$-dimensional cube, its influence is the average of its influences in the two restrictions obtained by fixing the first coordinate to $1$ and to $-1$.

**Proof.** Write the influence as the uniform average of the indicator that the coordinate is pivotal. A uniform sign vector in dimension $n+1$ can be averaged by first fixing its initial coordinate to $1$ or to $-1$; the expectation decomposition for a sign cube states that the full average is the mean of these two restricted averages (\texttt{FABL.expect_fin_cons}). In either slice, flipping the chosen later coordinate leaves the first coordinate fixed, so the pivotal event is exactly the pivotal event for the corresponding restricted function. Substituting these two slice averages gives the claimed formula.

**Key facts.** `FABL.expect_fin_cons`.
