<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_poly_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of tape and head bounds

**Claim.** If every work tape has the prescribed unary content and head positions satisfy the bounds for the current stage, then after one step the tape contents are unchanged and the new stage and head positions satisfy the corresponding bounds.

**Proof.** Read the symbol under each head from the assumed tape contents: it is true exactly when that head lies in $[0,q)$. If the machine is halted, the configuration is unchanged, so both conclusions persist. Copy and setup stages are impossible under the assumed head invariant. It remains to check the loop, rewind, advance, and emit transitions.

In a loop stage at index $i$, if tape $i$ is blank then its head must be at or beyond the right endpoint $q$; the loop bounds force it to equal $q$. The machine moves that head left into the rewind stage, while the other heads stay fixed and retain the required strict upper bounds and nonnegativity. If tape $i$ is not blank, all heads are in $[0,q)$. The transition leaves them fixed and moves to the preceding loop index, or to the emit stage at the terminal index; these bounds imply the required bounds in either successor stage.

In a rewind stage, if tape $i$ is blank, its head is outside $[0,q)$ and the rewind bounds force it to be $-1$. The machine moves it right and enters the next advance stage; the other heads are nonnegative and remain below $q$. If tape $i$ is not blank, it lies in $[0,q)$, so the machine moves it left and stays in rewind; the bounds on all heads are preserved. In an advance stage, when the index is still within the tape range, the selected head moves right and the machine enters the corresponding loop stage; the advance bounds ensure the loop bounds. At the terminal index the machine halts, and the existing bounds imply the halted-state bounds. Finally, in an emit stage the heads do not move; either successor state has the same required interval bounds. In every case the transition only moves heads and does not write on the tapes, so their contents remain the prescribed unary tapes.
