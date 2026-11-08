<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityOptimality.lean :: FABL.booleanInfluence_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of the First Coordinate

**Claim.** For a sign-valued function on the $(n+1)$-dimensional cube, the influence of the first coordinate is the probability that the two restrictions obtained by fixing that coordinate to opposite signs disagree.

**Proof.** Express the influence as the uniform average of the pivotal-event indicator, then decompose that average into the two slices where the first coordinate is respectively $1$ and $-1$ (\texttt{FABL.expect_fin_cons}). On either slice, flipping the first coordinate compares the same tail vector evaluated under the two opposite restrictions. Hence the pivotal event on each slice is exactly that those restricted functions disagree. The two slice averages are consequently equal, and their average is the probability of this disagreement.

**Key facts.** `FABL.expect_fin_cons`.
