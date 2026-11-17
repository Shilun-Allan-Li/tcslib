<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.sq_fourierCoeff_le_restrictedFourierWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient Bounded by Restricted Weight

**Claim.** If $S$ is the part of $U$ lying in $J$, then the square of the Fourier coefficient of $f$ at $U$ is at most the restricted Fourier weight on $J$ at $S$.

**Proof.** Let $T$ be the part of $U$ outside $J$. The decomposition of a frequency into its portions in and outside $J$ gives $U$ as the union of the lifted free frequency $S$ and the lifted fixed frequency $T$ (`liftFreeFrequencyPart_union_liftFixedFrequencyPart`); the hypothesis identifies the free portion with the specified $S$. Hence the squared coefficient at $U$ is one term in the sum defining the restricted Fourier weight. Every term of that sum is a square and is therefore nonnegative, so the selected term is at most the entire sum.

**Key facts.** `FABL.liftFreeFrequencyPart_union_liftFixedFrequencyPart`.
