<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.heads_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Casting an Updated Register Assignment

**Claim.** Casting each value to an integer after replacing register $t$ by $m$ gives the same function as first casting all register values to integers and then replacing the value at $t$ by $m$.

**Proof.** Compare the two functions at an arbitrary register index $i$. If $i=t$, both updates return the replacement value $m$, cast to an integer. If $i\ne t$, both updates retain the original value $\rho(i)$, and both sides cast it to an integer. The functions therefore agree at every index.
