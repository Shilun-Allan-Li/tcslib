<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DiscreteDerivatives.lean :: FABL.fourierCoeff_singleton_eq_of_transitiveSymmetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal Singleton Coefficients by Symmetry

**Claim.** If a Boolean function is transitive symmetric, then its singleton Fourier coefficients at any two coordinates are equal.

**Proof.** Transitive symmetry supplies a coordinate permutation sending $i$ to $j$ and preserving the function under the corresponding input permutation. The Fourier coefficient transformation law says that composing with this input permutation transports the coefficient at a frequency to the coefficient at its inverse-permuted frequency (`fourierCoeff_comp_permuteInput`). Apply it to the singleton frequency at $j$. Since the function is unchanged, the coefficient there equals the coefficient at the inverse image of $j$, which is $i$.

**Key facts.** `FABL.fourierCoeff_comp_permuteInput`.
