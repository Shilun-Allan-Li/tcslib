<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.fourierOneNormClass_work_polynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial work bound

**Claim.** For $s\ge 0$ and $0<\varepsilon\le 1/2$, every supported outcome of the query-mode Kushilevitz–Mansour program with $M=\max\{1,\lceil4s^2/\varepsilon\rceil\}$ has work at most $2^{66}(n+1)^3(s+1)^{16}/\varepsilon^{18}$.

**Proof.** The general work bound for the program gives, after casting its rational inequality to the reals, work at most $2^{42}(n+1)^3(M+1)^8/\varepsilon^{10}$ (`kushilevitzMansourProgramForBound_work_polynomial_cast_le`). The family-size estimate, using $s\ge0$, gives $M+1\le 6(s+1)^2/\varepsilon$ (`fourierOneNormFamilySizeBound_add_one_cast_le`). Raising this nonnegative inequality to the eighth power and substituting into the work bound yields a coefficient factor $2^{42}6^8$, a factor $(s+1)^{16}$, and denominator $\varepsilon^{18}$. Since $6^8\le 2^{24}$, the coefficient is at most $2^{66}$. Positivity of $\varepsilon$ follows from its parameter bounds (`positiveLearningParameter_toReal_mem_Ioc`), justifying the divisions and power comparison.

**Key facts.** `FABL.kushilevitzMansourProgramForBound_work_polynomial_cast_le`, `FABL.fourierOneNormFamilySizeBound_add_one_cast_le`, `FABL.positiveLearningParameter_toReal_mem_Ioc`.
