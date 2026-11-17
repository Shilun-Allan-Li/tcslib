<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.call_le_stepsPerStep_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound for call-step cost

**Claim.** Under the given bounds on $pos,size,r,b$, the total call-step cost is at most $2n(a+2+k)$.

**Proof.** Rewrite the right side using distributivity and the definition of the per-step bound $2n$: it is $2na+4n+2nk$. The hypothesis on $b$ bounds it by $2nk$, and $r\le n$. Also, $pos+size+2\le n$ implies $pos+size+1\le n-1$, so $2(pos+size+1)\le 2n$. These estimates bound the left side by $size+2nk+n+2n+2$. The same position hypothesis gives $size+2\le n$, and therefore this is at most $2nk+4n$, which is no greater than $2na+4n+2nk$ since $a\ge0$.
