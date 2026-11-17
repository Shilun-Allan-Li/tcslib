<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.isKJunta_one_of_fourierWeightAtMost_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree mass forces a junta

**Claim.** If a Boolean function has all its Fourier weight on levels at most one, then it depends on at most one coordinate.

**Proof.** Split according to whether some singleton Fourier coefficient has square equal to $1$. In that case, choose such a coordinate $i$. Parseval’s identity says that the sum of the squares of all Fourier coefficients is $1$; since the coefficient at $\{i\}$ already contributes $1$, the sum over every other set is zero. Each summand is nonnegative, so every other Fourier coefficient vanishes. Thus the level-one Fourier weight is exactly $1$, and the characterization of Boolean functions with all their level-one weight shows that $f$ is either the dictator on some coordinate $j$ or its negative. In either case, agreement of two inputs on coordinate $j$ forces their function values to agree, so $f$ is a $1$-junta.

Otherwise every singleton coefficient has square different from $1$. The zero-or-one alternative for each singleton coefficient then forces all singleton coefficients to vanish. Coefficients on sets of size greater than one vanish by the low-degree weight hypothesis. Hence every nonempty-set coefficient is zero. The Fourier expansion now shows that the real encoding of $f$ is constant. Since the real sign encoding is injective, $f$ itself is constant, and therefore depends on at most zero coordinates (in particular, at most one).

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`, `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.eq_dictator_or_neg_dictator_of_fourierWeightAtLevel_one_eq_one`, `FABL.singletonCoeff_sq_eq_zero_or_one_of_fourierWeightAtMost_one_eq_one`, `FABL.fourierCoeff_eq_zero_of_fourierWeightAtMost_one_eq_one`, `FABL.fourier_expansion`, `FABL.signValue_injective`.
