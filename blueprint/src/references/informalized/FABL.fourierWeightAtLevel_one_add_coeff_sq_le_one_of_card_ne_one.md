<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.fourierWeightAtLevel_one_add_coeff_sq_le_one_of_card_ne_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier weight bound away from level one

**Claim.** If $f$ is sign-valued and $S$ has cardinality other than one, then its level-one Fourier weight plus $\widehat f(S)^2$ is at most one.

**Proof.** Let $\mathcal L$ be the family of all singleton subsets. Since $|S|\ne1$, the set $S$ is not in $\mathcal L$. Thus adjoining $S$ to $\mathcal L$ gives a subfamily of all subsets of coordinates. Every squared Fourier coefficient is nonnegative, so the sum over this subfamily is at most the sum over all subsets. Parseval's identity for a sign-valued function (`sum_sq_fourierCoeff_eq_one`) says the latter sum is $1$. The sum over $\mathcal L$ is exactly the level-one weight, yielding the inequality.

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`.
