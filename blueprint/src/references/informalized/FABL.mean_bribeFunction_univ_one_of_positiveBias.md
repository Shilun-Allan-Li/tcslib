<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_bribeFunction_univ_one_of_positiveBias -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Bias Forces the Top Value

**Claim.** If $f$ is monotone and has positive bias, then forcing every coordinate to $1$ makes the mean equal to $1$.

**Proof.** The value of $f$ at the all-$1$ input is either $1$ or $-1$. If it were $-1$, every input would have output at most $-1$ by monotonicity, since every sign-coordinate is at most $1$. As $-1$ is the least sign, $f$ would be constantly $-1$. Such a function has no inputs with value $1$, so its positive bias is zero, a contradiction. Therefore $f$ takes value $1$ at the all-$1$ input. Bribing every coordinate sets the input to this point, making the bribed function constantly $1$; its mean is consequently $1$.

**Key facts.** `FABL.sign_le_one`, `FABL.neg_one_le_sign`.
