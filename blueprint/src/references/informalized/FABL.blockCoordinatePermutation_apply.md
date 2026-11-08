<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Examples.lean :: FABL.blockCoordinatePermutation_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action of a block coordinate permutation

**Claim.** The permutation induced by $\sigma$ and $\tau$ sends the coordinate corresponding to $(i,j)$ to the coordinate corresponding to $(\sigma(i),\tau(j))$.

**Proof.** The permutation is defined by first converting a coordinate in $\mathrm{Fin}(sw)$ to its pair of indices, applying the product permutation $(i,j)\mapsto(\sigma(i),\tau(j))$, and converting the pair back to a coordinate. Applying this composite to the coordinate of $(i,j)$ cancels the conversion with its inverse and gives the coordinate of $(\sigma(i),\tau(j))$.
