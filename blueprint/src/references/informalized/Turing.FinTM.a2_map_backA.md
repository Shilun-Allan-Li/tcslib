<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_backA -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return through the first buffer

**Claim.** For $j\le |a|$, after $j+1$ steps from the specified backward-through-the-first-buffer configuration, the machine is in the emit state with both buffer heads at $0$ and all other listed data unchanged.

**Proof.** Induct on $j$. For $j=0$, the first buffer head is at $-1$, where the buffer is blank (`Turing.FinTM.bufferTape_left`). The machine therefore takes the transition into the emit state and moves that head one position to $0$. The explicit configuration update is given by `Turing.FinTM.a2_map_move`; zero simulated time leaves the starting configuration unchanged (`Turing.MultiTapeTM.runFrom_zero`), and the successor-time run rule accounts for the single step (`Turing.MultiTapeTM.runFrom_succ_eq_step`).

For the successor case, suppose the head starts at $j$, where $j<|a|$. The cell there contains $a[j]$: at a natural-number position the buffer tape agrees with list lookup (`Turing.FinTM.bufferTape_nat`), and the length bound ensures the lookup exists. In state `backA`, the machine sees this symbol and moves the head one position left while remaining in `backA`. The movement's effect on the configuration is described by `Turing.FinTM.a2_map_move`; the induction hypothesis applies to the resulting configuration. The successor-time run rule completes the step count, and the bound needed for the induction hypothesis follows from $j+1\le |a|$.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.a2_map_move`.
