<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.length_searchState_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Search state gate bound

**Claim.** If every circuit at an index from $1$ through $M$ has size at most $S$, then after $j\le M$ search steps the gate list in the state has length at most $1+j(S+1)$.

**Proof.** Induct on $j$. Initially the state contains one gate, giving the bound at $j=0$. For the successor step, the state construction appends the embedded gates for circuit $D(j+1)$. The length of that embedded list is the circuit's gate count plus one (`length_embedGates`). Since the circuit has $n+j+1$ inputs, the size bound gives $n+j+1+|(D(j+1)).gates|\le S$. Thus each step adds at most $S+1$ gates. Combining this with the induction bound gives $1+j(S+1)+(S+1)=1+(j+1)(S+1)$; the hypotheses apply because $j+1\le M$.

**Key facts.** `BoolCircuit.length_embedGates`.
