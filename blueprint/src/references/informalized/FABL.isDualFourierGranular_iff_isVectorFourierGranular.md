<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.isDualFourierGranular_iff_isVectorFourierGranular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalence of Fourier Granularity Conditions

**Claim.** For every $n$, real-valued function on $\mathbb F_2^n$, and real $\varepsilon$, dual Fourier granularity is equivalent to vector Fourier granularity, or equivalently granularity of the corresponding function on the sign cube.

**Proof.** First use `isVectorFourierGranular_iff` to express sign-cube granularity as the assertion that every vector frequency has a Fourier coefficient equal to an integer multiple of $\varepsilon$. For the forward implication, given a vector frequency $\gamma$, apply dual granularity to the corresponding linear functional `vectorDualEquiv n γ`. The coefficient identity `dualFourierCoeff_vectorDualEquiv` identifies this dual coefficient with the vector Fourier coefficient, so the same integer witness proves the desired assertion. Conversely, given a dual functional $\psi$, take its corresponding vector frequency under the inverse equivalence, apply vector granularity, and use the same coefficient identity in reverse. Thus the two conditions are equivalent.

**Key facts.** `FABL.isVectorFourierGranular_iff`, `FABL.dualFourierCoeff_vectorDualEquiv`.
