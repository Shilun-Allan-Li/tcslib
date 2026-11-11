<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean :: Complexity.PathHard.matrix_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting of the matrix computation

**Claim.** Starting from the matrix-computation state with the stated register conditions, the program halts while all registers remain bounded by $B$. Its answer is true in true mode; in false mode it is the edge predicate for the source and target vertices determined by $i$ and $e$.

**Proof.** In true mode the matrix state returns true immediately. The initial configuration satisfies the register guard by the bound on the starting state, so the immediate-return property (`AHalt.ret`) gives halting with the required guard.

In false mode, put $j=\floor{i/2}$. The first machine step takes the computation from the matrix state to the program point that halves the offset; the guard is preserved at this step (`stepH_of`). The program then copies $j$ into the source register, sets its scratch counter to $e$, and uses the repeated-halving routine to replace the source register by $u_0=\floor{j/2^e}$ (`cp_run`, `hv_run`). It copies $u_0$ to a scratch register and multiplies it by $2^e$ using the shift routine (`sh_run`). Subtracting this product from $j$ leaves the remainder $v_0=j-u_0 2^e=j\bmod 2^e$ (`sb_run` and the division algorithm). The dispatch routine therefore halts with the answer for the edge from $u_0$ to $v_0$ (`dispatch_halt`). Since these are exactly the quotient and remainder appearing in the claim, this is the required answer. The cited routines maintain the register bound throughout their runs, and the guard at the starting and intermediate states follows from the given register bounds.

**Key facts.** `Complexity.PathHard.gb_of`, `Complexity.LogProg.AHalt.ret`, `Complexity.LogProg.AReach.halt`, `Complexity.PathHard.stepH_of`, `Complexity.PathHard.cp_run`, `Complexity.PathHard.hv_run`, `Complexity.PathHard.sh_run`, `Complexity.PathHard.sb_run`, `Complexity.PathHard.dispatch_halt`.
