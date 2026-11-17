<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.queryCount_majorityThreeTree12 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third majority tree query count

**Claim.** For every sign-valued input on three coordinates, the third majority tree makes two queries when \(x_1=x_2\), and three when \(x_1\ne x_2\).

**Proof.** Consider whether the signs at the first two queried coordinates, 1 and 2, are equal. If they are, the tree stops after two queries; otherwise it queries the remaining coordinate, giving three. Thus its query count is the claimed conditional value.
