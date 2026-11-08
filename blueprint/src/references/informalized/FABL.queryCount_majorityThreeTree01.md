<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.queryCount_majorityThreeTree01 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First majority tree query count

**Claim.** For every sign-valued input on three coordinates, the first majority tree makes two queries when \(x_0=x_1\), and three when \(x_0\ne x_1\).

**Proof.** Split into the two possibilities for whether the first two queried signs agree. If they agree, the tree stops after those two queries. If they differ, it queries the third coordinate, for three queries total. These are exactly the two values in the stated formula.
