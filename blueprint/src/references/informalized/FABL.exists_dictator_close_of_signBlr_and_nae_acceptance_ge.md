<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.exists_dictator_close_of_signBlr_and_nae_acceptance_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Dictator Near the Function

**Claim.** If the BLR and NAE testers each accept a Boolean function with probability at least $1-\varepsilon/10$, where $0\le\varepsilon\le1$, then the function is within relative Hamming distance $\varepsilon$ of some dictator.

**Proof.** First use the identity between the NAE tester's acceptance probability and the Condorcet-winner probability (`FABL.naeFunctionTester_acceptanceProbability`). Together with the bound that this probability is at most $7/9+(2/9)W_1[f]$ (`FABL.condorcetWinnerProbability_le`), the NAE acceptance assumption gives $W_1[f]\ge1-9\varepsilon/20$. The BLR closeness theorem supplies a set $S$ for which $f$ is within relative Hamming distance $\varepsilon/10$ of the parity on $S$ (`FABL.exists_parity_close_of_signBlr_acceptanceProbability_ge`). The uniform inner-product identity, and the facts that parity has real representation equal to its monomial (`FABL.parityFunction_toReal`) and that a Fourier coefficient is the uniform inner product with the corresponding monomial (`FABL.fourierCoeff_eq_uniformInner`), then give $\widehat f(S)\ge1-\varepsilon/5$.

Suppose $|S|\ne1$. The level-one Fourier weight plus the square of this coefficient is at most $1$ for such a set (`FABL.fourierWeightAtLevel_one_add_coeff_sq_le_one_of_card_ne_one`). Because $0\le\varepsilon\le1$, the coefficient lower bound is nonnegative, so squaring it yields $W_1[f]+(1-\varepsilon/5)^2\le1$. Combining this with $W_1[f]\ge1-9\varepsilon/20$ forces $1\ge2-17\varepsilon/20$. Since $\varepsilon\le1$, the right side is at least $23/20>1$, a contradiction. Hence $|S|=1$, so $S=\{i\}$ for some coordinate $i$. Parity on this singleton is the dictator at $i$. The distance bound to that parity is at most $\varepsilon/10\le\varepsilon$, as required.

**Key facts.** `FABL.naeFunctionTester_acceptanceProbability`, `FABL.condorcetWinnerProbability_le`, `FABL.exists_parity_close_of_signBlr_acceptanceProbability_ge`, `FABL.uniformInner_eq_one_sub_two_mul_relativeHammingDist`, `FABL.parityFunction_toReal`, `FABL.fourierCoeff_eq_uniformInner`, `FABL.fourierWeightAtLevel_one_add_coeff_sq_le_one_of_card_ne_one`.
