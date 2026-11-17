<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.condorcetWinnerProbability_le_of_equalSingletonFourierCoefficients -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Condorcet Winner Probability Bound

**Claim.** If all singleton Fourier coefficients of a Boolean rule are equal and $n>0$, then its three-candidate Condorcet winner probability is at most $\frac79+\frac{4}{9\pi}+\frac{2}{3n}$.

**Proof.** First bound the Condorcet winner probability by $\frac79+\frac29$ times the level-one Fourier weight (`condorcetWinnerProbability_le`). Equal singleton coefficients, together with $n>0$, give the level-one weight bound $2/\pi+3/n$ (`fourierWeightAtLevel_one_le_two_div_pi_add_three_div_card`). Since $2/9$ is positive, substituting this upper bound preserves the inequality. Expanding gives $\frac79+\frac{4}{9\pi}+\frac{2}{3n}$, as claimed.

**Key facts.** `FABL.condorcetWinnerProbability_le`, `FABL.fourierWeightAtLevel_one_le_two_div_pi_add_three_div_card`.
