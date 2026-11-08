<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_boundary_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Step Boundary Operation

**Claim.** Starting in state $0$, the boundary machine reaches state $3$ after three steps, writes $b$ one cell left of the initial head position, and moves the selected head right by one; it reaches state $3$ no earlier, and its heads satisfy the stated bounds.

**Proof.** Let $p$ be the initial position of tape $i$. The first transition moves that head left and changes the state from $0$ to $1$ (`Turing.step_of_tapeAction_move`), so it is at $p-1$. The second transition writes $b$ at its current cell, moves right, and enters state $2` (`Turing.step_of_tapeAction_write`); the head is back at $p$. The third transition moves right again and enters state $3$ (`Turing.step_of_tapeAction_move`), leaving the head at $p+1$. The tape updates therefore put $b$ at $p-1$. Before the third transition the states are $0$, $1$, and $2$, so state $3$ has not yet been reached. At the intermediate times the selected head is at $p$, $p-1$, $p$, or $p+1$, while all other heads are stationary; this proves the head bounds.

**Key facts.** `Turing.step_of_tapeAction_move`, `Turing.step_of_tapeAction_write`.
