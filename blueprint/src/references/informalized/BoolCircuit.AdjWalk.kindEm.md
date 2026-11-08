<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.kindEm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Gate Kind Walk

**Claim.** When the gate at vertex $V$ is $g$, the walk processes the two-bit encoding of its kind from position $k$. It returns the appropriate bit if the target position is within those two bits, and otherwise reaches the stated postcondition; the registers remain bounded by $B$.

**Proof.** The gate lookup identifies the kind of vertex $V$ (`vtype_gate`). Begin by applying the register bound (`gd_rg`) and unfold the first call in the walk: the oracle asks whether $V$ has kind AND (`orc_type`). Split into the three possible gate kinds.

If $g$ is AND, the oracle answers yes. The walk emits the two bits of the AND encoding in sequence, using `Em.emit` for each bit; their concatenation gives the required behavior.

If $g$ is OR, the AND query answers no, and the subsequent OR query answers yes. The walk consequently emits the two OR bits. If $g$ is NOT, both the AND and OR queries answer no, after which the walk emits the two NOT bits. In each case, concatenating the emitted one-bit behaviors proves the result for the full two-bit encoding (`Em.append`). The register bounds required at each transition follow from the hypotheses and the register-tuple bound.

**Key facts.** `BoolCircuit.AdjWalk.gd_rg`, `BoolCircuit.AdjWalk.Em.step`, `BoolCircuit.AdjWalk.astep_call₁`, `BoolCircuit.AdjWalk.orc_type`, `BoolCircuit.AdjWalk.vtype_gate`, `BoolCircuit.AdjWalk.Em.emit`, `BoolCircuit.AdjWalk.Em.append`, `BoolCircuit.AdjWalk.Em.mono`.
