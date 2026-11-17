<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_seek_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outward positioning scan

**Claim.** Starting in the seek-left phase with guide head at $0$, the simulator reaches the forward phase with guide head at $-R$ after exactly $R+2$ steps, leaving the other specified data and output unchanged.

**Proof.** First prove by induction on $n\le R+1$ that after $n$ steps the machine is still in the seek-left phase and its guide head is at $-n$. The zero-step case is the initial configuration. For the induction step, the guide head is at $-n$, which is not the left edge at $-R-1$ when $n<R+1$. The guide tape therefore presents no left-edge marker, so the schedule controller remains in seek-left and moves one position left. The exact one-step description for the decorated simulator (`dataCfg_step`) reduces this transition to the schedule controller's transition and shows that the data-state registers, data tapes, and output are unchanged. The guide tape reports its left-edge marker precisely at coordinate $-R-1$ (`guideTape_left`), and the fixed-guide hypothesis is transported to the macrostep configuration by `macroCfg_guide`; the controller's seek transition is then given by `macroCfg_seek`. At $n=R+1$, the guide head is at $-R-1$, so one final step recognizes the left edge, changes phase to forward, and moves the guide head right to $-R$. Combining this step with the $R+1$-step induction run gives the claimed $R+2$ steps. The run identities used to combine successive steps are the zero-run, successor-step, and iteration laws for `runFrom`.

**Key facts.** `Complexity.dataCfg_step`, `Complexity.guideTape_left`, `Complexity.macroCfg_guide`, `Complexity.macroCfg_seek`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
