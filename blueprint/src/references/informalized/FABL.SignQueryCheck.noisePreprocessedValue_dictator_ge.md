<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignQueryCheck.noisePreprocessedValue_dictator_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator Noise Bound

**Claim.** For a sign query check of arity $m$, noise preprocessing with parameter $\delta\in[0,1]$ lowers the dictator's randomized value by at most $m\delta/2$.

**Proof.** Let $v_j$ be the dictator's sign at the $j$th query. On these deterministic signs, the predicate accepts with probability exactly the indicator of whether it accepts $(v_j)_j$; this is the sign-input evaluation identity (`SignPredicate.randomizedValue_signValues`). The predicate's scaled-sign bound (`SignPredicate.randomizedValue_scaled_sign_ge`) says that replacing each $v_j$ by a sign of mean $(1-\delta)v_j$ decreases that indicator by at most $m\delta/2$. It remains to identify these scaled means with the values supplied by the noised dictator. Preprocessing agrees with applying the noise operator to the function (`SignQueryCheck.noisePreprocessedValue_eq_noiseOperator`). The dictator is the singleton Walsh monomial (`dictator_toReal_eq_monomial_singleton`), and the noise operator multiplies a monomial of degree one by $1-\delta$ (`noiseOperator_monomial_apply`). Thus at every query the noised dictator has value $(1-\delta)v_j$, so the scaled-sign bound gives the claimed inequality.

**Key facts.** `FABL.SignPredicate.randomizedValue_signValues`, `FABL.SignPredicate.randomizedValue_scaled_sign_ge`, `FABL.SignQueryCheck.noisePreprocessedValue_eq_noiseOperator`, `FABL.dictator_toReal_eq_monomial_singleton`, `FABL.noiseOperator_monomial_apply`.
