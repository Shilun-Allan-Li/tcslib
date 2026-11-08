<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_simulate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Time Simulation of the Source Machine

**Claim.** For every source time $t\le\tau$, the source configuration has a valid finite window and the simulator reaches its encoding by some time $u\le\sigma_k(t)$, with its work head throughout the run between the encoded window bounds $ak-1$ and $(a+n)k$.

**Proof.** Proceed by induction on $t$. At time zero, choose the initial window $[0,1)$ and the initial simulation time $2k+2$. The initial-window lemma (`dgWindow_init`) supplies the window conditions, and the initialization span (`dg_init`) supplies the encoded configuration and head bound. For the successor step, take the inductive window $[a,a+n)$ and its simulator span. The live-state hypothesis ensures that the source configuration at time $t$ has a state $q$, so its transition action is defined and the one-step run equation identifies the next configuration with the action applied to the current one. Determine the two boundary-growth booleans from whether the transition sends a head across the left or right window boundary. The window-update lemma (`dgWindow_step`) gives the enlarged valid window, and the one-step simulation lemma (`dg_step`) runs the simulator from the old encoding to the new one. Its span is first widened to cover the old interval bounds using `dgSpan_mono`, then concatenated with the inductive span using `dgSpan_add`. The elapsed simulation time increases by the one-step cost; `dgCost_le` bounds that increment by the recurrence defining the next simulation-time bound. The resulting window and span establish the successor case.

**Key facts.** `Turing.FinTM.dgWindow_init`, `Turing.FinTM.dg_init`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.dgWindow_step`, `Turing.FinTM.dg_step`, `Turing.FinTM.dgSpan_mono`, `Turing.FinTM.dgSpan_add`, `Turing.FinTM.dgCost_le`.
