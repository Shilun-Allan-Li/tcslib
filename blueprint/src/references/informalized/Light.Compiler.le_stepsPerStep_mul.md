<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.le_stepsPerStep_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplicative Step Bound

**Claim.** If $a\le n$ and $1\le c$ for natural numbers $a,c,n$, then $a\le (2n)c$.

**Proof.** Since $a\le n\le 2n$, we have $a\le (2n)\cdot 1$. Multiplication by the nonnegative number $2n$ preserves the inequality $1\le c$, giving $(2n)\cdot 1\le (2n)c$. Transitivity proves the claim.
