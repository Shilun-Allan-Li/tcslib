<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.biasedFourierCoeff_singleton_eq_of_transitiveSymmetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Coefficients Under Transitive Symmetry

**Claim.** If $f$ is invariant under coordinate permutations that can carry any coordinate to any other, then its biased Fourier coefficients on any two singleton sets are equal.

**Proof.** Transitivity supplies a permutation $\sigma$ carrying $i$ to $j$ under which $f$ is invariant. Consequently, composing $f$ with the input permutation leaves $f$ unchanged. The coefficient permutation identity (`biasedFourierCoeff_comp_permuteInput`), applied at $\{j\}$, says that the coefficient of this composition at $\{j\}$ equals the coefficient of $f$ at $\sigma^{-1}(\{j\})$. Since $\sigma(i)=j$, this preimage is $\{i\}$. Replacing the composition by $f$ gives the desired equality.

**Key facts.** `FABL.biasedFourierCoeff_comp_permuteInput`.
