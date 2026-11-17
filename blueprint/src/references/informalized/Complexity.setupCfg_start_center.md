<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_start_center -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return to the Guide Origin

**Claim.** Starting in start-center phase with guide head at $-j$ and guide tape of radius $R$, after $j+1$ steps the machine is in macrostep-check phase with guide head at $0$, with all other configuration data unchanged.

**Proof.** First determine one step for each $j$. The guide symbol at the head is the origin exactly when the head position is $0$ (`guideTape_origin`). Thus, when $j=0$, the start-center transition recognizes the origin, enters macrostep-check, and leaves all heads and tapes fixed. When $j>0$, the guide head is not at the origin, so the transition remains in start-center and moves it one cell right, from $-j$ to $-(j-1)$; the other data stay fixed. Induction on $j$ now gives the stated run: for $j=0$, the one-step run is the required transition, using the zero-step and successor-step descriptions of a run (`Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`). For the successor case, take the first rightward step just described, then apply the induction hypothesis to the remaining $j+1$ steps.

**Key facts.** `Complexity.guideTape_origin`, `Complexity.setupCfg_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
