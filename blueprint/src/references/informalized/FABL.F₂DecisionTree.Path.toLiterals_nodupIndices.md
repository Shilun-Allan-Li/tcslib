<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.F₂DecisionTree.Path.toLiterals_nodupIndices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct indices in path literals

**Claim.** The coordinate indices in the list of literals associated with a path are pairwise distinct.

**Proof.** The list of literal indices is identified directly with the list of coordinates obtained by attaching membership proofs to the elements of the path support and then forgetting those proofs. The attached list has no repetitions because it lists the elements of a finite set. Moreover, forgetting the membership proofs is injective on these attached elements: if their underlying coordinates agree, the two subtypes are equal. An injective map preserves the absence of repetitions, so the list of literal indices is duplicate-free.
