<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.embedAll_range'_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Embedding of a Circuit List

**Claim.** Embedding a list of circuits with source vertices shifted by $B$ and offset $B+L$ gives the same gate list as embedding with the original source vertices and offset $L$, then adding $B$ to each argument vertex of every gate.

**Proof.** First compare the vertex maps. If $v<m$, the source list beginning at $B$ sends $v$ to $B+v$, while the source list beginning at $0$ sends it to $v$; hence the former embedding map at offset $B+L$ is $B$ plus the latter map at offset $L$. If $v\ge m$, both maps use the offset branch, and the same identity follows by arithmetic.

Now induct on the circuit list. For the empty list both embedded lists are empty. For a nonempty list, split off its first circuit. The recursive embedding of the remaining circuits agrees by the induction hypothesis, since their offsets differ by the same shift $B$. For the first circuit, remapping each argument by the vertex-map identity agrees with shifting the original remapped argument. Deduplicating arguments preserves this equality because addition by $B$ is injective, so shifting a list and then removing repetitions is the same as removing repetitions first and then shifting. The extra output gate agrees by the same vertex-map identity. Combining the first circuit's gates and output gate with the recursive remainder proves the result.
