<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.positive_familyBound_of_spectrum_concentrated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Family Size Bound

**Claim.** If the family has size at most $M$ and the Fourier weight outside it is at most $varepsilon/4$, for a parameter $0<varepsilon\le\tfrac12$, then $M>0$.

**Proof.** Assume $M=0$. Since the family has nonnegative cardinality and its cardinality is at most $M$, the family is empty. The total Fourier weight outside the empty family is the sum of all squared Fourier coefficients, which equals $1$ by Parseval's identity (`sum_sq_fourierCoeff_eq_one`). The concentration assumption would therefore imply $1\le\varepsilon/4$. But the parameter satisfies $0<\varepsilon\le 1/2$ (`positiveLearningParameter_toReal_mem_Ioc`), so $\varepsilon/4\le 1/8$, a contradiction. Thus $M>0$.

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`, `FABL.positiveLearningParameter_toReal_mem_Ioc`.
