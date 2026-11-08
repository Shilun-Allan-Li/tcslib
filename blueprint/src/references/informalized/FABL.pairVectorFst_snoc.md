<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pairVectorFst_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First coordinates of an appended pair vector

**Claim.** Taking first coordinates of the vector obtained by appending a pair gives the vector of first coordinates with the appended pair's first coordinate appended.

**Proof.** Equality of vectors follows by checking each index. An index in $\mathrm{Fin}(n+1)$ is either the final index or comes from an index in $\mathrm{Fin}(n)$. At the final index, the appended pair contributes its first coordinate. At every earlier index, appending leaves the original pair unchanged, so taking its first coordinate gives the corresponding entry of the original first-coordinate vector.
