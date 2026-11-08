<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loop_input_move_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step Input-head Movement Bound

**Claim.** For $n\in\mathbb{N}$, a position $p$ among the $n+2$ input-head positions, and a movement sign $m\in\{-1,0,1\}$, the clamped new position is at most $p+1$.

**Proof.** Split into the three possible movement signs. A zero movement leaves the position unchanged, and a negative movement has value $p-1$ (`Turing.FinTM.moveInputPos_neg_val`), so each satisfies the bound. For a positive movement, if $p$ is the right boundary $n+1$, the head is clamped there and the bound follows directly (`Turing.moveInputPos_rightBoundary`). Otherwise the new position is exactly $p+1$ (`Turing.moveInputPos_pos_of_ne_right`), giving equality in the desired bound.

**Key facts.** `Turing.FinTM.moveInputPos_neg_val`, `Turing.moveInputPos_rightBoundary`, `Turing.moveInputPos_pos_of_ne_right`.
