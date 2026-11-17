<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.tendsto_log_div_sq_atTop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm Divided by a Square

**Claim.** As $t$ tends to $+\infty$, $\log(t)/t^2$ tends to zero.

**Proof.** The standard logarithmic limit gives $\log(t)/t\to0$ as $t\to+\infty$. Also, $1/t\to0$. Their product therefore tends to zero. For nonzero $t$, this product equals $\log(t)/t^2$, so the two functions agree eventually along the filter at infinity and have the same limit.
