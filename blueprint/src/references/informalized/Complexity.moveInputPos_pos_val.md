<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.moveInputPos_pos_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Position After a Positive Move

**Claim.** For a valid head position $q$ among the $n+2$ positions, moving in the positive direction produces the natural-number position $\min(q+1,n+1)$.

**Proof.** Represent the position by its natural-number value $q$, with $q<n+2$. A positive move adds $1$ and converts the result to a natural number, giving $q+1$. If this value is less than $n+2$, it is at most $n+1$, so the position is $q+1=\min(q+1,n+1)$. Otherwise it must equal $n+2$, since $q<n+2$; the move's boundary rule then returns $n+1$, again equal to the stated minimum.
