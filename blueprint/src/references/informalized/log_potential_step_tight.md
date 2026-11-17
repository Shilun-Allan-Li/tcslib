<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Regret.lean :: log_potential_step_tight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tight one-step Hedge bound

**Claim.** For a valid loss sequence and positive learning rate, the change in log potential at round $t$ is at most $-\eta\widehat{\ell}_t+\eta^2/8$.

**Proof.** The potentials at times $t$ and $t+1$ are positive, so their log difference is the logarithm of their ratio. Write $\mu=\widehat{\ell}_t$. Validity of the losses implies $0\le\mu\le1$ (`hedgeLoss_nonneg`, `hedgeLoss_le_one`). The one-step potential ratio bound (`potential_ratio_le`) gives a ratio at most $1-(1-e^{-\eta})\mu$, which equals $(1-\mu)+\mu e^{-\eta}$. Monotonicity of the logarithm therefore bounds the log ratio by $\ln((1-\mu)+\mu e^{-\eta})$. Hoeffding's lemma (`hoeffding_lemma`), applied with $p=\mu$ and $h=-\eta$, bounds this by $-\eta\mu+\eta^2/8$, proving the claim.

**Key facts.** `potential_pos`, `potential_ratio_le`, `hedgeLoss_nonneg`, `hedgeLoss_le_one`, `hoeffding_lemma`.
