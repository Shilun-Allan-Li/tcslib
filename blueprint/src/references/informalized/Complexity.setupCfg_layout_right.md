<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_layout_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Rightward Allocation Pass

**Claim.** From layout-right phase $0$, with unary head at $1$ and guide head at $0$ on the partial guide with $n+1$ copied cells, after $3B+2$ steps the machine is in layout-return phase $0$, with unary head at $B$, guide head at $3B$, and guide tape equal to the right guide of radius $3B$; all other configuration data is unchanged.

**Proof.** Apply the layout-prefix formula (`Complexity.setupCfg_layout_prefix`) through $3B$ steps. The hypothesis $n+1\le B$ ensures its guide-filling condition holds, so the guide tape at that point is `copyGuide (3B)`; the phase index is $0$, the unary head is $B+1$, and the guide head is $3B$. The next layout-end step (`Complexity.setupCfg_layout_end`) writes an interior marker at the guide head and moves the unary head as specified for phase $0$. By `copyGuide_next`, this write extends the copy guide to `copyGuide (3B+1)`. The right-edge transition (`Complexity.setupCfg_right_edge`) then enters layout-return phase $0$, decreases the unary head to $B$, decreases the guide head to $3B$, and marks the right edge. By the definition of `rightGuide`, these tape contents form the right guide of radius $3B$. The two successor-step identities (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) account for these final two transitions after the prefix.

**Key facts.** `Complexity.setupCfg_layout_prefix`, `Complexity.setupCfg_layout_end`, `Complexity.copyGuide_next`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.setupCfg_right_edge`.
