<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.eventually_inv_two_pow_le_two_mul_log_dimension_div_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes Dimension Logarithmic Bound

**Claim.** For all sufficiently large integers $w$, $2^{-w}\leq 2\log(D_w)/D_w$, where $D_w$ is the critical dimension defined from the largest critical tribes size up to $2^{w+2}$.

**Proof.** Eventually, the power identity expresses $2^w$ as $D_w/\log D_w$ times $1+e_w$, where the relative error $e_w$ tends to zero. Also, $D_w$ tends to infinity, so eventually $D_w>1$ and hence $\log D_w>0$. Since $e_w\to0$, eventually $1+e_w>1/2$. Inverting the positive power identity gives $2^{-w}=\log D_w/[D_w(1+e_w)]$, which is at most $2\log D_w/D_w$ by the lower bound on $1+e_w$.

**Key facts.** `FABL.eventually_two_pow_eq_dimension_div_log_mul_one_add_error`, `FABL.tendsto_tribesCriticalPowerRelativeError_zero`, `FABL.tendsto_tribesCriticalDimension_atTop`.
