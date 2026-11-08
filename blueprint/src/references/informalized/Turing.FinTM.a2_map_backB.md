<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_backB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return through the second buffer

**Claim.** For $j\le |b|$, after $j+1$ steps from the specified backward-through-the-second-buffer configuration, the machine enters the backward-through-the-first-buffer state with the second buffer head at $0$.

**Proof.** Induct on $j$. At $j=0$, the second buffer head is at $-1$, so its cell is blank (`Turing.FinTM.bufferTape_left`). The machine transitions from `backB` to `backA` and moves the second buffer head to $0$; `Turing.FinTM.a2_map_move` gives the resulting configuration, and the zero-time and successor-time run rules (`Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`) identify the run with that step.

For the successor case, the second buffer head starts at $j$, with $j<|b|$. Its cell contains $b[j]$, by the natural-position buffer lookup rule (`Turing.FinTM.bufferTape_nat`) and the length bound. In state `backB`, the machine moves that head one position left and remains in `backB`; the configuration update is given by `Turing.FinTM.a2_map_move`. Apply the induction hypothesis to this new configuration. The successor-time run rule yields the required total of $j+2$ steps, and $j+1\le |b|$ follows from the assumed bound.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.a2_map_move`.
