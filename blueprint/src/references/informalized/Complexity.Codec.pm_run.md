<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean :: Complexity.Codec.pm_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of a Head Movement

**Claim.** In step mode, the program reaches its next phase without changing the register file, and the phase records whether moving the input head from the current position, with boundary parameter $R.N1-1$, gives position $R.Pos2$.

**Proof.** Let $B$ be the stated register bound. The register bound hypothesis ensures that every register value is at most $B$; this is the register-file bound fact (`Regs.Bd.val_le`). We split according to the input-head movement in the action selected by $I$ and $b$.

If the movement is zero, the program compares $R.Pos$ with $R.Pos2$ directly and proceeds to `pmNext` with the comparison result. This instruction leaves all registers unchanged, and the two branches encode exactly whether the head's position remains $R.Pos$ and equals $R.Pos2$.

If the movement is positive, the program first compares $R.Pos$ with $R.N1$. When they are equal, the boundary rule prevents an increase, so it compares $R.Pos$ with $R.Pos2$ and proceeds with that result. Otherwise it increments $R.Pos$, compares the incremented position with $R.Pos2$, and then decrements $R.Pos$ to restore the original register file. The temporary increment remains within $B$: from $R.Pos\le R.N1$ and $R.N1+1\le B$, we get $R.Pos+1\le B$. Thus each intermediate configuration satisfies the register bound, and the final comparison is precisely the test that the bounded positive move gives $R.Pos2$.

If the movement is negative, the program tests whether $R.Pos=0$. At zero, the truncated move stays at zero, so it compares $R.Pos$ with $R.Pos2$ directly. Otherwise it decrements the position, compares the decremented value with $R.Pos2$, and increments the position again to restore the original registers. This temporary decrement preserves the bound, and the hypotheses $1\le R.N1$ and $R.Pos\le R.N1$ ensure the described move agrees with the stated boundary convention.

Each displayed instruction transition gives a one-step reachability fact (`Reach.single'`); the guard needed for each such step follows from the register bound and the applicable phase's precondition (`gd_of`). Composing these steps gives the required reachability (`Reach.trans`). The positive case's temporary register file is identified with the original one at the endpoint using the equality-preserving reachability rule (`Reach.cast`). In all three movement cases, the final phase is selected by the Boolean test that the prescribed moved position equals $R.Pos2`, and the endpoint register file is again $R.val$.

**Key facts.** `Complexity.Codec.Regs.Bd.val_le`, `Complexity.Codec.gd_of`, `Complexity.Codec.Reach.single'`, `Complexity.Codec.Reach.trans`, `Complexity.Codec.Reach.cast`.
