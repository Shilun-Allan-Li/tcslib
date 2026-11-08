<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.walk_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Termination of the Circuit Walk

**Claim.** For a canonical circuit, the walk on the paired unary input and binary index halts with the specified encoding bit (combined with $\ell$ when the index is in range), or false when it is out of range; before halting, every register stays bounded by the encoding length.

**Proof.** Write $B$ for the encoding length. Canonicality identifies the output vertex with the last circuit vertex, and the circuit encoding decomposes into the unary input-length prefix, the encoded gates, and the unary output-vertex suffix. The encoding-length lower bound for a list encoding, together with the positive circuit size, gives the bounds needed to keep the walk’s registers at most $B$ throughout.

Starting from the all-zero registers, the walk first validates the paired input. The input’s binary payload is canonical because it is the binary representation of $i$. The initial state transition is handled by the one-step halting invariant, while the subsequent trace is divided, in order, into the input-length loop, the gate-processing loop, and the output-suffix loop. The loop lemmas establish these traces with bounded registers: the input loop arrives at the first gate, the gate loop advances through the encoded gates and leaves the walk at the output-suffix state, and the output loop ends at the done state. Their traces are joined using the concatenation property of the execution invariant.

The gate-loop endpoint records the relevant index and bounded auxiliary registers. Updating coordinate $3$ preserves the register tuple’s displayed form, and the coordinate formula identifies its value when the output loop begins. Applying the output loop then yields the done state with bounded registers. By the definition of the oracle walk and the encoding-bit calculation in these loop invariants, when $i<B$ the final answer is $\ell\lor$ the $i$th encoding bit. When $i\ge B$, the walk reaches the same terminal form with answer false. The halting and register bounds follow from the execution invariant and the halting-step results.

**Key facts.** `BoolCircuit.DAGCircuit.encode_eq`, `BoolCircuit.length_encodeList_ge`, `BoolCircuit.AdjWalk.inLoop`, `BoolCircuit.AdjWalk.gLoop`, `BoolCircuit.AdjWalk.gd_rg`, `BoolCircuit.AdjWalk.upd_3`, `BoolCircuit.AdjWalk.rg_3`, `BoolCircuit.AdjWalk.oLoop`, `BoolCircuit.AdjWalk.Em.append`, `BoolCircuit.AdjWalk.Em.step`, `BoolCircuit.AdjWalk.rg_init`, `Complexity.LogProg.AHalt.step`, `Complexity.LogProg.canon_bits`, `Complexity.LogProg.AHalt.ret`.

**Caveat.** The supplied loop statements specify their endpoint invariants but omit the internal derivations that establish how those invariants encode the selected bit and the out-of-range answer.
