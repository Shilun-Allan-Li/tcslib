<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.eventually_two_pow_eq_dimension_div_log_mul_one_add_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic dimension identity

**Claim.** For all sufficiently large natural numbers $w$, the stated identity expresses $2^w$ as the critical dimension divided by its logarithm, multiplied by one plus the relative error.

**Proof.** Since the critical dimension tends to infinity, it is eventually greater than $1$. Fix such a $w$ and write $D$ for that dimension. Then $D>0$ and $\\log D>0$. By definition, the relative error is $2^w\log(D)/D-1$, so $1+E=2^w\log(D)/D$. Multiplying by $D/\log(D)$ gives the desired identity; the positivity facts ensure the divisions are legitimate.

**Key facts.** `FABL.tendsto_tribesCriticalDimension_atTop`.
