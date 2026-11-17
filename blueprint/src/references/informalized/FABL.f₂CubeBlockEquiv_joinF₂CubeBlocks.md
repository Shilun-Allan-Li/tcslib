<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.f₂CubeBlockEquiv_joinF₂CubeBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction of two binary blocks

**Claim.** Splitting the concatenation of $x$ and $y$ into its two length-$n$ blocks recovers $(x,y)$.

**Proof.** The concatenation is the inverse image of $(x,y)$ under the equivalence between length-$2n$ vectors and pairs of length-$n$ vectors. Applying that equivalence after its inverse recovers the original pair, by the inverse laws for an equivalence.
