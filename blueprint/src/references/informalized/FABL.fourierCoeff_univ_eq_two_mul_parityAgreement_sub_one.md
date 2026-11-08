<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.fourierCoeff_univ_eq_two_mul_parityAgreement_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full parity agreement identity

**Claim.** The Fourier coefficient of a Boolean function at the full coordinate set equals twice its agreement probability with full parity, minus one.

**Proof.** Let $g$ be the parity function on all coordinates. Its real-valued form is the monomial indexed by the full set (`FABL.parityFunction_toReal`). The Fourier coefficient therefore equals the uniform inner product of $f$ with $g$ (`FABL.fourierCoeff_eq_uniformInner`). This inner product is the probability that $f$ and $g$ agree minus the probability that they disagree (`FABL.uniformInner_eq_uniformProbability_eq_sub_ne`). Since agreement and disagreement partition the cube, these probabilities sum to $1$ (`FABL.uniformProbability_eq_add_ne`), so their difference is twice the agreement probability minus $1$.

**Key facts.** `FABL.parityFunction_toReal`, `FABL.fourierCoeff_eq_uniformInner`, `FABL.uniformInner_eq_uniformProbability_eq_sub_ne`, `FABL.uniformProbability_eq_add_ne`.
