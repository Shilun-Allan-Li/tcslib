<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/LaplacianAndPoincare.lean :: FABL.variance_eq_totalInfluence_toReal_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality in the Boolean Poincaré Inequality

**Claim.** For a Boolean function on the sign cube, its variance equals its total influence exactly when it is constant with value $1$ or $-1$, or is a dictator or the negative of a dictator.

**Proof.** Suppose first that variance equals total influence. The variance–influence equality criterion says this is equivalent to the Fourier weight on degrees at most one equaling the second moment (the criterion used in the proof is `variance_eq_totalInfluence_iff_lowDegreeWeight_eq_secondMoment`). Since every value of the function is a sign, its square is identically one, so the second moment is one. Thus its Fourier weight through degree one is one. The low-degree weight criterion then implies that the Boolean function depends on at most one coordinate (`isKJunta_one_of_fourierWeightAtMost_one_eq_one`). The classification of Boolean functions depending on at most one coordinate says it must be one of the two constants or a signed dictator (`eq_const_or_signedDictator_of_isKJunta_one`).

Conversely, constants have zero total influence and zero variance. A dictator has variance and total influence both equal to one (`variance_dictator`, `totalInfluence_dictator`). Negating a function preserves its variance and total influence (`variance_neg`, `totalInfluence_neg`), so the negative dictator also has both quantities equal to one.

**Key facts.** `FABL.variance_eq_totalInfluence_iff_lowDegreeWeight_eq_secondMoment`, `FABL.isKJunta_one_of_fourierWeightAtMost_one_eq_one`, `FABL.eq_const_or_signedDictator_of_isKJunta_one`, `FABL.totalInfluence_const`, `FABL.variance_dictator`, `FABL.totalInfluence_dictator`, `FABL.variance_neg`, `FABL.totalInfluence_neg`.
