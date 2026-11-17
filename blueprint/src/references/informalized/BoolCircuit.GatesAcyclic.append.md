<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.GatesAcyclic.append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity under concatenation

**Claim.** If every gate at position $i$ in $gs$ refers only to indices less than $n+i$, and every gate at position $i$ in $hs$ refers only to indices less than $n+|gs|+i$, then every gate at position $i$ in the concatenated list $gs$ followed by $hs$ refers only to indices less than $n+i$.

**Proof.** Fix a position $i$ in the concatenated list and an argument of the gate there. If $i<|gs|$, the gate at position $i$ is the one at position $i$ in $gs$, so its argument is less than $n+i$ by the acyclicity assumption on $gs$. Otherwise, the gate lies in $hs$ at position $i-|gs|$. The assumption on $hs$ bounds its argument by a number strictly less than $n+|gs|+(i-|gs|)=n+i$. Thus the required bound holds in either case.
