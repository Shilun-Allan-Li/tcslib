<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LearningModel.lean :: FABL.not_isFourierSpectrumConcentratedOn_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Mass Outside the Empty Family

**Claim.** For any sign-valued Boolean function and rational $\varepsilon$ with $0<\varepsilon\le1/2$, its Fourier weight outside the empty family is not at most $\varepsilon/2$.

**Proof.** Outside the empty family includes every frequency, so Parseval’s identity (`sum_sq_fourierCoeff_eq_one`) gives total Fourier weight exactly $1$. If the weight were at most $\varepsilon/2$, then $1\le\varepsilon/2$. But the parameter condition (`positiveLearningParameter_toReal_mem_Ioc`) gives $\varepsilon\le1/2$, hence $\varepsilon/2\le1/4$, a contradiction.

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`, `FABL.positiveLearningParameter_toReal_mem_Ioc`.
