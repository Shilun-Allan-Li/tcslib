<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Scan.lean :: Turing.scan_fold_trace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Fold Machine Trace

**Claim.** Starting in the forward phase with accumulator $a_0$ and the input head at position $1$, the fold machine follows the forward configurations carrying the fold of each scanned prefix, then the backward configurations carrying the fold of all of $x$, and finally the stationary done configuration carrying that full fold.

**Proof.** The forward configuration at index $0$ agrees with the given initial configuration because the empty prefix folds to $a_0$ and the input head is at position $1$. The general trace theorem therefore applies once the transitions in the forward, turn, return, entry, and stationary phases are checked (`catalog_trace_run`). At forward index $r<|x|$, the input head reads $x[r]$ (`inputSymbolInner`). The machine moves right and updates its state by applying $\delta$ to the fold of the first $r$ symbols and $x[r]$; the fold-of-an-appended-element identity identifies this with the fold of the first $r+1$ symbols. Thus the next configuration is the stated forward configuration (`step_of_inputMoveAction`). At the end of the input, the machine moves left into the backward phase, carrying the fold of the entire word. At each backward index $r+1$, it reads $x[r]$, moves left, and remains in the backward phase with that same full fold; these are exactly the backward configurations in reverse index order (`inputSymbolInner`, `step_of_inputMoveAction`). At backward index $0$, the input symbol is absent, and one rightward transition enters the done phase carrying the full fold (`step_of_inputMoveAction`). The done configuration is fixed by the machine's zero-movement transition (`step_of_inputMoveAction`). The input-head position updates follow the formulas for moving right away from the boundary and moving left (`moveInputPos_pos_of_ne_right`, `Turing.FinTM.moveInputPos_neg_val`).

**Key facts.** `Turing.catalog_trace_run`, `Turing.inputSymbolInner`, `Turing.step_of_inputMoveAction`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.moveInputPos_neg_val`.
