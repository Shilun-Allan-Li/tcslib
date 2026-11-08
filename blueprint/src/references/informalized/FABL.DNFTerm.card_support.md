<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.card_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support size equals term width

**Claim.** For a term with distinct literal coordinates, the number of coordinates in its support equals its width.

**Proof.** The support is the set of coordinates obtained by mapping the list of literals to their indices and then taking the resulting finite set. Because these indices are pairwise distinct, converting their list to a finite set preserves the list's length. The list of indices has the same length as the literal list, which is the term's width. Therefore the support cardinality equals the width.
