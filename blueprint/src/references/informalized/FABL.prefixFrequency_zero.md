<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.prefixFrequency_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty zero prefix

**Claim.** For any $n$ and any subset $U$ of $\mathrm{Fin}(n)$, the elements of $U$ whose indices are less than zero form the empty set.

**Proof.** No natural-number index is less than zero. Thus the filter defining the prefix retains no elements of $U$, and the prefix is empty.
