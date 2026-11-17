<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineSmall.lean :: BoolCircuit.exists_straightLine_length_le_size_of_le_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-input straight-line simulation

**Claim.** For $1\le n\le 2$, every directed acyclic Boolean circuit on $n$ inputs has an equivalent valid straight-line program of length at most the circuit's size.

**Proof.** First suppose the circuit output vertex is an input, say input $k$. Use a one-statement program that ANDs the same literal $x_k$ with itself. The one-line evaluation formula shows that this outputs $x_k$, and the circuit input-value identity (`values_getD_input`) shows that the circuit does too. Its length is one, within the circuit size. Otherwise the output is not an input, so the output-vertex bound forces the circuit size to be at least $n+1$. Since $1\le n\le2$, either $n=1$ or $n=2$. For $n=1$, apply the one-line representation theorem (`exists_oneLine`) to the circuit's Boolean function; for $n=2$, apply the three-line representation theorem (`exists_threeLine`). Their lengths, respectively one and three, are within the circuit size in these cases. In each case the chosen program computes the circuit's function.

**Key facts.** `BoolCircuit.DAGCircuit.values_getD_input`, `BoolCircuit.oneLine_eval`, `BoolCircuit.oneLine_length`, `BoolCircuit.exists_oneLine`, `BoolCircuit.exists_threeLine`.
