<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.layer1Function_hasWidthLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-layer gate width bound

**Claim.** For a first-layer gate, its computed function has a representation of width at most the circuit width, with the representation type determined by the dual of the first-layer gate: a DNF for an AND gate and a CNF for an OR gate.

**Proof.** Consider the two possible first-layer gate types. If the gates are AND gates, represent the selected gate by the DNF consisting of the single term stored for that gate. The selected term occurs among the circuit’s first-layer terms, so its width is at most the DNF width of the whole first layer (`DNFFormula.width_le_of_mem`). The single-term DNF evaluates exactly as that gate. If the gates are OR gates, use the CNF consisting of the single clause stored for the selected gate. Its width is again bounded by the first-layer width, and its evaluation agrees with the gate’s clause evaluation. These two constructions give the representation required by the formal statement, which uses the dual gate type.

**Key facts.** `FABL.DNFFormula.width_le_of_mem`.

**Caveat.** The supplied informal statement describes the representation types without the dualization appearing in the formal statement. The account follows the formal statement and proof: AND gives DNF, and OR gives CNF.
