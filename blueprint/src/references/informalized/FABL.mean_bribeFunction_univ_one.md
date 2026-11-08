<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_bribeFunction_univ_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full Positive Bribery Gives Constant Output

**Claim.** If $f$ is monotone and its mean is at least $-99/100$, then forcing every coordinate to $1$ makes the mean equal to $1$.

**Proof.** The value of $f$ at the all-$1$ input is a sign, hence is either $1$ or $-1$. If it is $-1$, then every input is coordinatewise at most the all-$1$ input, because each sign is at most $1$. Monotonicity therefore implies that $f(x)\le -1$ for every input; since $-1$ is also the least sign, $f$ is constantly $-1$. Its mean would then be $-1$, contradicting the assumed lower bound $-99/100$. Thus $f$ takes value $1$ at the all-$1$ input. Bribing every coordinate produces exactly that input regardless of the original $x$, so the bribed function is constantly $1$ and has mean $1$.

**Key facts.** `FABL.sign_le_one`, `FABL.neg_one_le_sign`.
