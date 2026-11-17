<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.disjoint_liftFreeFrequency_liftFixedFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Lifted Frequencies

**Claim.** For a subset $J$ of the coordinate set, the images in the full coordinate set of any set of coordinates in $J$ and any set of coordinates outside $J$ are disjoint.

**Proof.** Suppose a coordinate belonged to both lifted sets. Membership in each image gives an original index from the corresponding set, and both indices map to that same full coordinate. Hence they are equal as coordinates. But the first index belongs to $J$, whereas the second lies outside $J$; equality would make the second belong to $J$, a contradiction.
