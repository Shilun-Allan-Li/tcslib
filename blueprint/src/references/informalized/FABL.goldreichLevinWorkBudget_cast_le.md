<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Resources.lean :: FABL.goldreichLevinWorkBudget_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin Work Budget Bound

**Claim.** For every nonnegative integer $n$ and rational threshold $0<\tau\le1$, the rational-valued Goldreich–Levin work budget is at most $2^{25}n(n+1)^2/\tau^8$.

**Proof.** Write $m$ for the sample count used by the estimator. Its positivity implies $m+1\le 2m$. The sample-count bound gives $m\le5120(n+1)(A+1)/\tau^4$, where $A$ is the active cap; the active-cap estimates give $A\le8/\tau^2$ and $A+1\le9/\tau^2$. Since $0<\tau\le1$, powers of $\tau$ satisfy $\tau^8\le\tau^4$, so the reciprocal fourth-power terms can be bounded by reciprocal eighth-power terms. The controller-step work is consequently at most $1296(n+1)^2/\tau^8$. For the estimator contribution, substitute the bounds on $A$ and $m+1$ into $16nA(m+1)(n+1)$; this is at most $11796480n(n+1)^2/\tau^8$, which is at most $2^{24}n(n+1)^2/\tau^8$. Adding the controller and estimator contributions yields a coefficient $1296+2^{24}$, at most $2^{25}$.

**Key facts.** `FABL.fourierEstimatorSampleCount_pos`, `FABL.goldreichLevinSampleCount_cast_le`, `FABL.goldreichLevinActiveCap_cast_le`, `FABL.goldreichLevinActiveCap_add_one_cast_le`.
