<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/CorrelationImmunityBounds.lean :: FABL.not_three_large_of_eq_symmDiff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three Sets Cannot All Be Large

**Claim.** If $S=T\mathbin{\triangle}U$, then $S,T,U$ cannot all have cardinality greater than $2n/3$.

**Proof.** The cardinality bound for two subsets and their symmetric difference gives $|T|+|U|+|T\mathbin{\triangle}U|\le 2n$ (`FABL.card_add_card_add_card_symmDiff_le_two_mul_dimension`). Since $S=T\mathbin{\triangle}U$, this is $|S|+|T|+|U|\le 2n$. But the three strict hypotheses imply $3|S|+3|T|+3|U|>6n$, hence their sum is greater than $2n$, contradicting the bound.

**Key facts.** `FABL.card_add_card_add_card_symmDiff_le_two_mul_dimension`.
