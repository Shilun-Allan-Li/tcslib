<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding length bound

**Claim.** For a directed acyclic circuit with $n$ input vertices, gates in topological order, and a valid output vertex, suppose each gate has distinct input vertices, every NOT gate has exactly one input, and each gate has at most two inputs. If its size is $n$ plus the number of gates, then its encoding has length at most twelve times the square of its size.

**Proof.** 1. First, the circuit size is at least $1$: the valid output index is strictly less than the size, which rules out size zero. Write $S$ for the size. Each gate's input vertices are below $S$, and the encoding of a vertex below $S$ has length at most $S$. The list-encoding bound says that encoding a list of $m$ objects whose individual encodings have length at most $B$ takes length at most $m(B+1)+1$ (`length_encodeList_le`). Applying it to a gate's arguments, which number at most two, and adding the fixed-length encoding of its gate kind shows that each gate encoding has length at most $2S+5$.

2. Apply the same list-encoding bound to the list of gates. There are at most $S$ gates, so this bounds the gate-list portion of the circuit encoding. The remaining portion encodes the output vertex, whose index is below $S$. Combining these bounds with the encoding definition, and using that both the number of gates and the number of inputs are at most $S$, gives the stated upper bound $12S^2$.

**Key facts.** `BoolCircuit.length_encodeList_le`.
