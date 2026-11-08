<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.mem_tabPre -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the Constant-Gate Prefix

**Claim.** Every gate in the list consisting of a false constant gate, a true constant gate, one constant gate for each entry of a Boolean list $z$, and then $W$ false constant gates is itself a constant gate.

**Proof.** An element of the concatenated list must come from one of its constituent parts. In the initial two-element list it is one of the false or true constant gates. In the mapped portion it is the image of some Boolean entry $b$ under the constant-gate construction, so it equals the constant gate for $b$. In the replicated portion every entry is the false constant gate. Each possibility therefore has the required form.
