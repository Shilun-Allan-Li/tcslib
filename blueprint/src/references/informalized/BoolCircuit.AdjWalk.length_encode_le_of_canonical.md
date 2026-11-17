<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.AdjWalk.length_encode_le_of_canonical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Encoding Length Bound

**Claim.** If each gate's argument list is strictly increasing and the output vertex has index $\mathrm{size}(C)-1$, then the encoding of $C$ has length at most $4(\mathrm{size}(C)+1)^3$.

**Proof.** Write $S=\mathrm{size}(C)$. First bound the encoding of each gate. If a gate occurs at position $j$, acyclicity says each of its arguments is less than $n+j$, hence less than $S$. Its arguments form a strictly increasing list, so they have no repetitions; as a list of distinct numbers below $S$, its length is at most $S$. Encoding each argument in binary uses at most $S$ bits, and the list-encoding bound from `length_encodeList_le'` therefore bounds the encoded argument list by $S(S+1)+1$. A gate-kind encoding has length $2$, so the full gate encoding has length at most $S(S+2)+3$. Apply the list-encoding bound again to the list of gates: there are at most $S$ gates, and each encoded gate has length at most $S(S+2)+3$. Finally, the circuit encoding also includes the encodings of the input count and output index. Each is at most $S$ bits, since both numbers are below $S$ (the output condition gives the latter). Combining these contributions and expanding gives an upper bound no larger than $4(S+1)^3$, as claimed.

**Key facts.** `BoolCircuit.AdjWalk.length_encodeList_le'`.
