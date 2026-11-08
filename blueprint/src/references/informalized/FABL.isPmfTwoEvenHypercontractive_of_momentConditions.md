<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.isPmfTwoEvenHypercontractive_of_momentConditions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment conditions imply hypercontractivity

**Claim.** The stated second-moment normalization, vanishing odd moments, even-moment bounds, and bound on $\rho^2$ imply the $2$-to-$2r$ hypercontractive inequality for every real $a,b$.

**Proof.** Fix real $a,b$. The first odd-moment condition gives $\mathbb E[X]=0$. The moment comparison theorem then bounds the $2r$-th moment of $a+\rho bX$ by $(a^2+b^2)^r$ (FABL.affine_evenMoment_le_of_momentConditions). By the even-power identity for the $2r$-norm, this is an upper bound for the $2r$-th power of that norm (FABL.pmfLpNorm_rpow). Meanwhile, the centered second-moment formula identifies the $2$-norm of $a+bX$ with $\sqrt{a^2+b^2}$ (FABL.pmfLpNorm_two_affine_centered), whose $2r$-th power is $(a^2+b^2)^r$. Both norms are nonnegative, so taking the $2r$-th root of the moment inequality proves the desired norm inequality. Since $a,b$ were arbitrary, hypercontractivity follows.

**Key facts.** `FABL.affine_evenMoment_le_of_momentConditions`, `FABL.pmfLpNorm_rpow`, `FABL.pmfLpNorm_two_affine_centered`, `FABL.pmfLpNorm_nonneg`.
