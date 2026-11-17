<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.sh_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Shift Run

**Claim.** If all registers of $st$ are at most $B$, its scratch register is zero, and the selected register times $2^c$ is at most $B$, then the program has a finite guarded run through shift operation $k$. At the exit, the counter register is cleared and the selected register has been multiplied by $2^c$, with every other register unchanged.

**Proof.** The nine shift phases implement repeated doubling. The loop first tests the counter; if it is zero, it exits. Otherwise it decrements the counter and tests the selected register. For each unit of that register, it decrements the selected register and adds two units to the scratch register. Once the selected register is exhausted, it transfers the scratch value back by decrementing the scratch register and incrementing the selected register twice per unit. This restores the selected register at twice its previous value and returns to the counter test. Since the counter began at $c$, after $c$ iterations it is zero and the selected value is its original value multiplied by $2^c$; the scratch register is again zero, and other registers are untouched. The hypothesis that the final product is at most $B$ bounds the selected register throughout, since its intermediate values do not exceed that final product; the counter, scratch register, and unchanged registers remain bounded as well. The general shift-loop result `Complexity.LogProg.shl_run` supplies this finite guarded run. The coordinate bound follows from `St.Bd.toV`, while `sh_ne` provides the pairwise distinctness needed to ensure the loop updates the intended registers independently.

**Key facts.** `Complexity.PathHard.sh_ne`, `Complexity.PathHard.St.Bd.toV`, `Complexity.LogProg.shl_run`.
