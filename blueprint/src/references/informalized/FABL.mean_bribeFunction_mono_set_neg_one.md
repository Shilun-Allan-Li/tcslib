<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_bribeFunction_mono_set_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity under Negative Bribery

**Claim.** If $f$ is monotone and $J\subseteq K$, then forcing the coordinates in $K$ to $-1$ gives a mean no larger than forcing only the coordinates in $J$ to $-1$.

**Proof.** Fix an input $x$. We compare the two bribed inputs coordinate by coordinate. If $i\in J$, then $i\in K$ as well, so both inputs have value $-1$ at $i$. If $i\notin J$ but $i\in K$, the input bribed on $K$ has value $-1$, which is at most the value in the input bribed on $J$, since $-1$ is the least sign. If $i\notin K$, both inputs retain $x_i$. Thus the input bribed on $K$ is coordinatewise at most the one bribed on $J$. Monotonicity of $f$ gives the same pointwise inequality for their outputs. Taking means preserves this inequality, by monotonicity of the mean on real-valued Boolean functions (FABL.mean_toReal_mono).

**Key facts.** `FABL.mean_toReal_mono`, `FABL.neg_one_le_sign`.
