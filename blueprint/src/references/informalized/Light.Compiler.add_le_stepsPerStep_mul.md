<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.add_le_stepsPerStep_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition bound for step counts

**Claim.** For natural numbers $a,b,c,k,n$, if $a\le n$, $1\le c$, and $b\le 2nk$, then $a+b\le 2n(c+k)$.

**Proof.** First, the step-count bound gives $a\le 2nc$ from $a\le n$ and $1\le c$ (\texttt{Light.Compiler.le_stepsPerStep_mul}). Combining this with $b\le 2nk$ yields $a+b\le 2nc+2nk$. Distributivity identifies the right side with $2n(c+k)$, proving the claim.

**Key facts.** `Light.Compiler.le_stepsPerStep_mul`.
