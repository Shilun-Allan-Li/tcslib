<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_bribeFunction_mono_set_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity under Positive Bribery

**Claim.** If $f$ is monotone and $J\subseteq K$, then forcing the coordinates in $J$ to $1$ gives a mean no larger than forcing the coordinates in $K$ to $1$.

**Proof.** Fix an input $x$. If $i\in J$, then $i\in K$, so both bribed inputs have value $1$ at $i$. If $i\notin J$ but $i\in K$, the input bribed on $J$ retains $x_i$, while the input bribed on $K$ has value $1$, which is at least $x_i$ since $1$ is the greatest sign. If $i\notin K$, both inputs retain $x_i$. Hence the input bribed on $J$ is coordinatewise at most the one bribed on $K$. Monotonicity of $f$ gives the corresponding pointwise inequality of outputs, and monotonicity of the mean gives the claimed inequality (FABL.mean_toReal_mono).

**Key facts.** `FABL.mean_toReal_mono`, `FABL.sign_le_one`.
