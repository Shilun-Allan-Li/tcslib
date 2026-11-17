<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/RandomSmallBias.lean :: FABL.two_pow_mul_two_exp_neg_four_mul_le_rpow_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential power bound

**Claim.** For each natural number $n\ge1$, $2^n\,2e^{-4n}\le 2^{-n}$.

**Proof.** Separate the case $n=1$. The inequality $e^4\ge8$ follows from $e>2$, which gives $e^4>16$, and hence in particular $e^4\ge8$. Rewriting the left side as $4/e^4$ shows it is at most $1/2=2^{-1}$.

If $n\ne1$, the assumption $n\ge1$ implies $n\ge2$. Since $-4n\le-2n$, monotonicity of the exponential gives $e^{-4n}\le e^{-2n}$. Multiplication by the positive factor $2^n\cdot2$ preserves the inequality. The resulting expression is at most $2^{-n}$ by the bound $2^n\,2e^{-2n}\le2^{-n}$ for $n\ge2$ (\texttt{FABL.two\_pow\_mul\_two\_exp\_neg\_two\_mul\_le\_rpow\_neg}).

**Key facts.** `FABL.two_pow_mul_two_exp_neg_two_mul_le_rpow_neg`.
