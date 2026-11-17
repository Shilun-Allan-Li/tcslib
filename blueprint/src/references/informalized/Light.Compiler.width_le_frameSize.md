<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.width_le_frameSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Statement Width Bound

**Claim.** For every program $P$ and every statement $b$ in $P$, the width of $b$ is at most the frame size of $P$.

**Proof.** By the characterization of a list maximum, `maxOf_le_iff` says that every element of $P$ has width at most `maxOf Stmt.width P` (apply it with that maximum as the bound). The frame size is the maximum of $3$ and this list maximum, so it is at least the list maximum. Combining these inequalities gives the desired bound.

**Key facts.** `Light.maxOf_le_iff`.
