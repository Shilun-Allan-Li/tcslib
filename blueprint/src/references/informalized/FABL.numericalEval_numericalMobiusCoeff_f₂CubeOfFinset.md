<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/NumericalNormalForm.lean :: FABL.numericalEval_numericalMobiusCoeff_f₂CubeOfFinset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Möbius coefficients recover indicator values

**Claim.** Evaluating the numerical polynomial with Möbius coefficients at the indicator vector of $U$ recovers the value of $\phi$ at that vector.

**Proof.** Evaluation at the indicator vector of $U$ first turns the polynomial into the sum of its coefficients over all $S\subseteq U$ (`numericalEval_f₂CubeOfFinset`). Substitute the defining formula for each Möbius coefficient. For each such $S$, rewrite its sum over $T\subseteq S$ as a sum over $T\subseteq U$ with the additional condition $T\subseteq S$, then interchange the finite sums. Fixing $T\subseteq U$, the remaining sum ranges over $S$ with $T\subseteq S\subseteq U$. The alternating subset sum over this interval is $1$ when $T=U$ and $0$ otherwise (`sum_Icc_neg_one_pow_card_sub`). Thus every term cancels except the one indexed by $T=U$, which contributes $\phi$ at the indicator vector of $U$.

**Key facts.** `FABL.numericalEval_f₂CubeOfFinset`, `FABL.sum_Icc_neg_one_pow_card_sub`.
