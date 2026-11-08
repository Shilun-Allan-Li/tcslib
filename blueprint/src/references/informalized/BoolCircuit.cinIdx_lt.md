<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.cinIdx_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Carry-In Index Bound

**Claim.** For all natural numbers $n$ and $i$, the recursively defined carry-in index satisfies $c_n(i)<n+2+15i$.

**Proof.** Split into the initial case and the successor case. At $i=0$, the index is $n$, which is less than $n+2$. At $i=j+1$, the defining equation gives $c_n(i)=n+2+15j+8$, while the claimed upper bound is $n+2+15(j+1)=n+2+15j+15$. The strict inequality follows from $8<15$.
