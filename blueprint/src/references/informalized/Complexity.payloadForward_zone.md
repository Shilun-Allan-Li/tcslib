<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.payloadForward_zone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward sweep over a zone

**Claim.** Folding the forward row transducer over the uncached zone of length $n$ starting at $z$, from register $f(z-1)$, produces register $f(z+n-1)$ and the cached zone of length $n$ starting at $z$.

**Proof.** Use induction on $n$, allowing $z$ to vary. For $n=0$, the zone is empty and the fold preserves its register; the claimed endpoint register is $f(z-1)$. For the step from $n$ to $n+1$, the first uncached row at $z$ is transformed by the one-row forward identity (payloadForward_row), producing register $f(z)$ and the cached row at $z$. The remaining fold is over the uncached zone of length $n$ starting at $z+1$. Its initial register is $f((z+1)-1)=f(z)$, so the induction hypothesis gives final register $f((z+1)+n-1)$ and the cached tail. Integer arithmetic identifies this register with $f(z+(n+1)-1)$; placing the first cached row before the tail gives the desired zone.

**Key facts.** `Complexity.payloadForward_row`.
