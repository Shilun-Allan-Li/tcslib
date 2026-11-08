<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.almostKWiseOutputMultiset_card_eq_source -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output multiset cardinality preservation

**Claim.** The cardinality of the output multiset equals the cardinality of the source multiset used to form it.

**Proof.** The output multiset is the list of transformed outputs, viewed as a multiset. A list's cardinality as a multiset is its length, and mapping a transformation over a list preserves length. The source multiset is likewise the original output list viewed as a multiset. Both cardinalities therefore equal the length of that original list.
