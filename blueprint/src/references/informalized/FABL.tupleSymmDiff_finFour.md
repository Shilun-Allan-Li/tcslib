<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.tupleSymmDiff_finFour -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric difference of four sets

**Claim.** For four finite subsets $S_0,S_1,S_2,S_3$, their tuple symmetric difference is $S_0\mathbin{\triangle}(S_1\mathbin{\triangle}(S_2\mathbin{\triangle}(S_3\mathbin{\triangle}\varnothing)))$.

**Proof.** By definition, the tuple symmetric difference is the left-associated list fold of symmetric difference over the tuple. Unfolding the four-entry list of the tuple gives $S_0\mathbin{\triangle}(S_1\mathbin{\triangle}(S_2\mathbin{\triangle}(S_3\mathbin{\triangle}\varnothing)))$, exactly the claimed expression.
