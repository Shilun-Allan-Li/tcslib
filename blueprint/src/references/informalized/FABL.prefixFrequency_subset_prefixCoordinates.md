<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.prefixFrequency_subset_prefixCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix frequency containment

**Claim.** The coordinates in a given set whose indices are less than $k$ are contained in the set of all coordinates whose indices are less than $k$.

**Proof.** Take any coordinate in the filtered subset. Its membership in the filter gives that its index is less than $k`; it is also a coordinate in the full coordinate set. These are exactly the membership conditions for the prefix coordinates, so the chosen coordinate belongs to that set.
