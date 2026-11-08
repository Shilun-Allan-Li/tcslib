<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.queryCount_majorityThreeTree02 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second majority tree query count

**Claim.** For every sign-valued input on three coordinates, the second majority tree makes two queries when \(x_0=x_2\), and three when \(x_0\ne x_2\).

**Proof.** Split according to whether the first two queried signs, at coordinates 0 and 2, agree. Agreement makes the tree stop after two queries; disagreement makes it query the remaining coordinate, for three. This gives the stated count in either case.
