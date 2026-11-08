<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.canonicalBlockTreeAux_wellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formedness of the Block Tree Construction

**Claim.** If every coordinate free in the starting restriction is available, then the tree constructed with any fuel is well formed relative to the available coordinates.

**Proof.** Induct on the fuel, with the restriction and available set generalized. At zero fuel the tree is a leaf, hence well formed. At successor fuel, split according to whether there is a compatible term. If not, the construction again gives a leaf. If there is one, let $T$ be the canonical term. When it has no free literal positions the tree is a leaf as well.

Otherwise, query the list of coordinates at its free literal positions. These coordinates are distinct, and each is free in the current restriction; the availability hypothesis therefore puts each in the available set. The lemma for querying a coordinate list then reduces well-formedness to the trees at the ends of the block, relative to the available set with those coordinates removed (`FABL.CoordinateDecisionTree.wellFormed_queryCoordinates`). For each assignment to the block, fixing its coordinates preserves the free-within condition for this reduced set (`FABL.CoordRestriction.freeWithin_fixCoordinateList`). If $T$ is compatible after those fixes, the branch is a leaf. Otherwise, it is the construction with one less fuel, so the induction hypothesis proves that branch well formed. This verifies both children throughout the block and completes the induction.

**Key facts.** `FABL.DNFTerm.coordinatesAtPositions_nodup`, `FABL.DNFTerm.coordinatesAt_freeLiteralPositions_all_free`, `FABL.CoordinateDecisionTree.wellFormed_queryCoordinates`, `FABL.CoordRestriction.freeWithin_fixCoordinateList`.
