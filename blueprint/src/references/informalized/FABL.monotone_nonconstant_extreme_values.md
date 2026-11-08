<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.monotone_nonconstant_extreme_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extreme Values of a Nonconstant Monotone Function

**Claim.** A nonconstant monotone sign-valued function takes value $-1$ at the all-$-1$ input and value $1$ at the all-$1$ input.

**Proof.** At the all-$-1$ input, the function value is either $-1$ or $1$. Suppose it were $1$. Every input lies above the all-$-1$ input, since $-1\le s$ for every sign $s$ (`neg_one_le_sign`). Monotonicity would then force the value at every input to be at least $1$, hence equal to $1` (`sign_eq_one_of_one_le`). This makes the function constant, contrary to hypothesis. Thus its value at the all-$-1$ input is $-1$. Similarly, every input lies below the all-$1$ input by the sign bound `sign_le_one`. If the function were $-1$ at that top input, monotonicity would force every value to be at most $-1$, hence equal to $-1` (`sign_eq_neg_one_of_le_neg_one`), again contradicting nonconstancy. So the top value is $1$.

**Key facts.** `FABL.neg_one_le_sign`, `FABL.sign_eq_one_of_one_le`, `FABL.sign_le_one`, `FABL.sign_eq_neg_one_of_le_neg_one`.
