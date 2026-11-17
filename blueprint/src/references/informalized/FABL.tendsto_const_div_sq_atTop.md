<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.tendsto_const_div_sq_atTop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal quadratic decay

**Claim.** For every real constant $c$, $c/t^2$ tends to zero as $t$ tends to $+\infty$.

**Proof.** As $t\to+\infty$, so does $t^2$, and the reciprocal of a function tending to $+\infty$ tends to zero. Multiplying this reciprocal by the fixed constant $c$ preserves convergence to zero.
