<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.exists_signedDictator_relativeHammingDist_eq_abs_fourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed dictator distance and Fourier coefficient

**Claim.** For a Boolean function and a coordinate, one of the dictator and its negation has relative Hamming distance from the function equal to half of one minus the absolute value of the corresponding singleton Fourier coefficient.

**Proof.** Let $c$ be the singleton Fourier coefficient. The real-valued dictator is the singleton monomial (`FABL.dictator_toReal_eq_monomial_singleton`), and the Fourier coefficient is therefore the uniform inner product of the function with that dictator (`FABL.fourierCoeff_eq_uniformInner`). For Boolean-valued functions, this inner product equals one minus twice their relative Hamming distance (`FABL.uniformInner_eq_one_sub_two_mul_relativeHammingDist`). If $c\geq0$, choose the unnegated dictator; solving that identity for the distance gives $(1-c)/2=(1-|c|)/2$. If $c<0$, choose the negated dictator. Negating a Boolean function negates its real-valued version (`FABL.BooleanFunction.toReal_neg`), so its inner product with the given function is $-c$. Applying the same distance identity to the negated dictator gives distance $(1-(-c))/2=(1-|c|)/2$, as required.

**Key facts.** `FABL.dictator_toReal_eq_monomial_singleton`, `FABL.fourierCoeff_eq_uniformInner`, `FABL.uniformInner_eq_one_sub_two_mul_relativeHammingDist`, `FABL.BooleanFunction.toReal_neg`.
