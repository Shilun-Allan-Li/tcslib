<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_log_tribesCriticalDimension_div_dimension_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Dimension Logarithmic Growth

**Claim.** For the critical dimension $D_w$, its logarithm divided by $D_w$ tends to zero as the width $w$ tends to infinity.

**Proof.** The real-variable limit $\log x/x\to0$ as $x\to\infty$ follows from the standard logarithm-versus-power asymptotic. The critical dimension tends to infinity as $w\to\infty$ (`tendsto_tribesCriticalDimension_atTop`). Composing the first limit with this divergence gives $\log D_w/D_w\to0$.

**Key facts.** `FABL.tendsto_tribesCriticalDimension_atTop`.
