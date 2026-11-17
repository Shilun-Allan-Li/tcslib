<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SpectralDegree.lean :: FABL.restrictionFourierCoeff_granular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Granularity of restricted coefficients

**Claim.** If every Fourier coefficient of the encoded function is an integer multiple of $\varepsilon$, then each coefficient of its restriction to fixed outside signs is also an integer multiple of $\varepsilon$.

**Proof.** Use the expansion of a restricted Fourier coefficient as a sum over all subsets $T$ of the fixed-coordinate index set: each summand is the ambient Fourier coefficient at the union of the lifted free frequency $S$ and lifted fixed frequency $T$, multiplied by the corresponding restricted-coordinate monomial (restrictionFourierCoeff_eq_sum). By the assumed ambient granularity, choose an integer $q_T$ so that this Fourier coefficient is $q_T\varepsilon$. Each monomial is integer-valued: its real value is the cast of the integer monomial (indexedMonomialInt_cast). Thus the restricted coefficient equals $\varepsilon$ times the integer sum $\sum_T q_T\,\mathrm{monomialInt}(T,z)$. This sum supplies the required integer multiplier.

**Key facts.** `FABL.restrictionFourierCoeff_eq_sum`, `FABL.indexedMonomialInt_cast`.
