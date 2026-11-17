<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.map_uniformPMF_finiteFamilyLinearToMatrixEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Distribution Under Matrix Indexing

**Claim.** For a finite family $\mathcal F$ of subsets of $\{1,\ldots,n\}$ and a natural number $m$, reindexing a uniformly chosen function from $\{1,\ldots,|\mathcal F|m\}$ to the Boolean cube as a function on $\mathcal F\times\{1,\ldots,m\}$ gives the uniform distribution on those functions.

**Proof.** The matrix-indexing construction is a bijection between the two finite function spaces: it first reindexes the domain by the bijection between the product index set and the finite index set, then curries the resulting function. Applying the uniform-distribution-under-bijection result (\texttt{map\_uniformPMF\_equiv}) to this bijection shows that the image distribution is uniform on the matrix-indexed function space.

**Key facts.** `FABL.map_uniformPMF_equiv`.
