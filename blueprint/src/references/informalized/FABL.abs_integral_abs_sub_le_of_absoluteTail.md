<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.abs_integral_abs_sub_le_of_absoluteTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First absolute moment from tail control

**Claim.** If two finite measures on the real line have integrable absolute-value functions, and their absolute-tail probabilities differ by at most an integrable bound $B(t)$ for every $t>0$, then the absolute difference of their first absolute moments is at most the integral of $B$ over the positive half-line.

**Proof.** For each measure, the layer-cake formula expresses its first absolute moment as the integral over $t>0$ of the measure of the set where $|x|>t$; these tail functions are integrable on the positive half-line (\texttt{FABL.integrableOn\_absoluteTail}). Subtract the two integral formulas and combine them into the integral of the difference of the tails. The absolute value of this integral is at most the integral of the absolute value of the tail difference. By the assumed pointwise tail bound, that integrand is at most $B(t)$ for every positive $t$. Monotonicity of integration therefore gives the claimed estimate.

**Key facts.** `FABL.integrableOn_absoluteTail`.
