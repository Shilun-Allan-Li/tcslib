<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_track_extent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on the visited interval

**Claim.** For each tape, the leftmost visited position is at most zero, the rightmost is at least zero, the current head lies between them, and the two bounds lie between $-t$ and $t$.

**Proof.** Proceed by induction on $t$. At time zero, both bounds and the head position are zero, so all the assertions hold. For the successor step, the head moves by at most one cell in absolute value: this follows from the one-step movement bound (`workTapePos_step_le`) together with the fact that running for $t+1$ steps is one step after running for $t$ (`runFrom_succ_eq_step'`). The new left bound is the minimum of the old left bound and the new head position, and the new right bound is their maximum. Thus zero remains between the bounds, the new head lies between them, and each bound can extend by at most one beyond its previous value. The induction hypotheses and the one-cell movement bound give the claimed bounds $-(t+1)$ and $t+1$.

**Key facts.** `Turing.MultiTapeTM.workTapePos_step_le`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
