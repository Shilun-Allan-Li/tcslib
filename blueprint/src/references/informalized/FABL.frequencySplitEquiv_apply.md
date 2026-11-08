<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.frequencySplitEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frequency Split Formula

**Claim.** Under the frequency split equivalence, a pair consisting of a subset of $J$ and a subset of the complementary coordinates corresponds to the union of those subsets, viewed in the full coordinate set.

**Proof.** Check membership of an arbitrary full coordinate in both sides. The equivalence first represents the pair as a disjoint union of a member from the $J$ side and a member from the complement side, then maps these to their original coordinates. In the forward direction, membership in this mapped disjoint union places the coordinate in one of the two parts, and the corresponding lift puts it in the stated union. Conversely, membership in either lifted set provides a member of the corresponding disjoint-sum part; the equivalence sends it back to that same coordinate. Thus the two finsets have identical members.
