<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.accIdx_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accumulator Index Bound

**Claim.** For all natural numbers $n$ and $i$, the accumulator index at step $i$ is less than $n+2+15i$.

**Proof.** Split into the initial step and a successor step. At $i=0$, the accumulator index is $n+1$, which is less than $n+2$. For $i=j+1$, its defining formula is $n+2+15j+14$, while the claimed upper bound is $n+2+15(j+1)=n+2+15j+15$. The former is one less than the latter, proving the bound.
