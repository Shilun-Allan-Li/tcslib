<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.coordinatesAtPositions_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct selected coordinates

**Claim.** For a conjunction whose literal coordinates are pairwise distinct, the coordinates at any selected set of literal positions are pairwise distinct.

**Proof.** The list of selected coordinates is obtained by mapping each selected position to its literal's coordinate. To show this map is injective on selected positions, suppose two positions give the same coordinate. Their indices in the full list of literal coordinates then agree; the no-duplicates hypothesis on that list implies the positions agree. A map that is injective on a noduplicated list of positions preserves the absence of repetitions, and the selected positions are noduplicated because they come from a finset.
