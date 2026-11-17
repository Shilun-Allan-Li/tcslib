<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf.lean :: Complexity.LogProg.TQBFARM.lv_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Through Literal Evaluation

**Claim.** With the scratch registers $T,Z,C$ initially zero and all registers bounded, the machine evaluates the current literal against the assignment encoded by $K,S$, returns the result at the clause state, and clears $V$.

**Proof.** Because the clause is not yet satisfied, the machine first copies $K$ into the counter register $C$ (`cp_run`), then runs the subtraction routine to replace $C$ by $K-V$ and clear $V$ (`sb_run`). If this difference is zero, then $V\ge K$, so the assignment at that variable is false by its definition. The machine takes the zero branch and returns the comparison of false with $b$, which is the desired literal value. If the difference is nonzero, then $V<K$. The machine decrements $C$ once, copies the stack $S$ into scratch register $T$, and halves $T$ by $2^C$ (`cp_run`, `hv_run`). The resulting quotient $q$ is at most $S$ and its parity is the bit of $S$ at position $K-1-V$. The assignment definition therefore gives $\mathrm{asg}(K,S,V)=\mathrm{decide}(q\bmod 2=1)$. The machine branches according to that parity and compares the resulting assigned bit with $b$, yielding the required Boolean. The register bounds for the intermediate states follow from the original bound and the arithmetic inequalities in the proof. In each branch the machine returns at the clause label with $V$ and $C$ zero and all other registers restored to their required values; the final state identifications complete the guarded run.

**Key facts.** `Complexity.LogProg.TQBFARM.cp_run`, `Complexity.LogProg.TQBFARM.sb_run`, `Complexity.LogProg.TQBFARM.hv_run`, `Complexity.LogProg.TQBFARM.step_of`, `Complexity.LogProg.TQBFARM.fin_of`.
