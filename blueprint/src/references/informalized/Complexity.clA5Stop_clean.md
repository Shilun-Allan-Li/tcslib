<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Stop_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Call Halts Under the Release Wrapper

**Claim.** If the original machine runs from the entry seam configuration to the specified exit seam configuration in positive time $t$, and does not reach the exit state at intermediate positive times, then the release wrapper reaches the corresponding halted configuration with its release flag true after $t+1$ steps.

**Proof.** Let $c$ be the original entry configuration. Since the run at time $t$ is live, the live-prefix lemma (\texttt{clA5\_live\_prefix}) shows that every configuration through time $t$ is live. We prove by induction on $v\le t$ that the wrapper’s run for $v$ steps is the original run for $v$ steps with release flag $\mathrm{decide}(v\ne0)$. At time zero this is the wrapper’s initial configuration. For a successor step, the original configuration is live; if the flag is already true, then $v>0$, and the hypothesis excludes the exit state at that intermediate time. The one-step wrapper identity (\texttt{clA5Stop\_step}) therefore advances the original configuration by one and sets the flag true. This proves the induction claim. At time $t$, positivity makes the flag true, and the original run is the specified exit configuration. One final step applies the wrapper’s release rule: at true flag and exit state it halts, preserving the tapes and output. The resulting configuration is exactly the asserted one.

**Key facts.** `Complexity.clA5_live_prefix`, `Complexity.clA5Stop_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
