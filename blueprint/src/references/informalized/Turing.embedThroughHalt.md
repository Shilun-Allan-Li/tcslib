<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedThroughHalt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation Through the Halting Step

**Claim.** Before time $T$, the run of $R$ agrees with the state-renamed embedding of the run of $M$; at time $T$ it has the designated return state. Before time $T$, its state is never that return state.

**Proof.** First, $T$ is positive: if $T=0$, then the time-zero halting assumption says that $c$ is halted, contradicting the hypothesis that its state is present. We prove by induction that for every $t<T$, the run of $R$ at time $t$ is the state-renamed image of $E(M^t(c))$. At time zero this is the initial configuration. For the induction step, write the run at time $t+1$ as one step after time $t$. By the induction hypothesis and the assumption that $M^t(c)$ is still live, the step-simulation hypothesis identifies this with the return encoding of $E(M^{t+1}(c))$. Since $t+1<T$, that latter configuration is live; the return encoding of a live configuration is exactly its state-renamed image. This proves the induction claim. To handle time $T$, use $T=(T-1)+1$ and apply the same step-simulation argument after the run equality at $T-1$. The result is the return encoding of $E(M^T(c))$. As the time-$T$ state of $M$ is absent, this encoding has state equal to the right-hand summand, as claimed. Finally, for each $t<T$, the run equality identifies the simulated state with the left-summand renaming of the state of $M^t(c)$. Such a state cannot be the right-summand return state, so the return state does not occur before time $T$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.embedReturnCfg_live`.
