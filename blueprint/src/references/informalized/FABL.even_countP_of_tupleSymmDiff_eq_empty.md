<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.even_countP_of_tupleSymmDiff_eq_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Membership Count

**Claim.** If the iterated symmetric difference of a finite tuple of sets is empty, then each element belongs to an even number of the sets.

**Proof.** For any element $x$, the parity of the number of sets containing $x$ is characterized by membership in their iterated symmetric difference: $x$ is absent from that difference exactly when the count is even (`not_mem_listSymmDiff_iff_even_countP`). The hypothesis says the iterated symmetric difference is empty, so $x$ is absent from it. The characterization therefore makes the count even.

**Key facts.** `FABL.not_mem_listSymmDiff_iff_even_countP`.
