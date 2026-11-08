<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.gLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Processing Loop

**Claim.** Under the stated canonicality and size bounds, the gate-processing walk processes the encoding of the remaining gates from vertex $V$. It returns the appropriate bit when the requested position lies in that encoding; once the position is past the encoding, it reaches the stated postcondition. Its registers remain bounded by $B$ throughout.

**Proof.** Proceed by induction on $d$, the number of vertices remaining before the circuit size. The argument maintains the position $k$ in the encoded output, the current vertex $V$, and the two auxiliary registers. The register bound at each transition follows from the coordinate bounds via the register-tuple bound (`gd_rg`), and `Em.step` lifts the established behavior back across that transition.

When $d=0$, the relation $V+d=\mathrm{size}(C_n)$ says that $V$ is the circuit size. There are no gates left to encode, so the remaining gate encoding is the one-bit terminator $[0]$. The size oracle confirms that $V$ is not a vertex of the circuit; the walk therefore emits the terminator bit and reaches the required postcondition with unchanged auxiliary registers.

For the inductive case, the gate at index $V-n$ exists. Split the remaining gate list into this gate followed by the later gates. Since its arguments are sorted and, by acyclicity, all arguments are less than $V$, filtering the vertices below $V$ by membership in its argument list recovers the argument list itself (`args_eq_filter`). Consequently the first gate's encoding consists of its leading marker, its two-bit kind encoding, and the encodings of its arguments, followed by the encoding of the remaining gates.

The walk first emits the marker. It then processes the two kind bits using the gate-kind behavior (`kindEm`). Next it scans the vertices below $V$ for the gate's arguments (`aLoop`), leaving the scan with the updated output position and a bounded auxiliary register. The induction hypothesis applies at vertex $V+1$ to the remaining gates; the arithmetic identity for the new output position matches the concatenated encoding. The concatenation principle for encoded walks (`Em.append`) combines these stages, yielding the claimed behavior for the entire suffix.

**Key facts.** `BoolCircuit.AdjWalk.gd_rg`, `BoolCircuit.AdjWalk.Em.step`, `BoolCircuit.AdjWalk.Em.emit`, `BoolCircuit.AdjWalk.Em.mono`, `BoolCircuit.AdjWalk.Em.append`, `BoolCircuit.AdjWalk.args_eq_filter`, `BoolCircuit.AdjWalk.kindEm`, `BoolCircuit.AdjWalk.aLoop`, `BoolCircuit.AdjWalk.astep_call₁`, `BoolCircuit.AdjWalk.orc_size`, `BoolCircuit.AdjWalk.rg_1`, `BoolCircuit.AdjWalk.upd_2`.
