<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.sealGates_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of gate sealing

**Claim.** If the original gate list is acyclic, its output is valid, and each index to be sealed is valid, then sealing produces an extension by strict gates that remains acyclic, has a valid output, and preserves the output value on every Boolean input.

**Proof.** Induct on the list of indices to be sealed. The empty list leaves the gates, output, and computed value unchanged, so all parts of the specification hold immediately.

For the inductive step, let $u$ be the first index and put $N=n+|gs|$. Append the sealing triple for $u$. The bounds on $u$ and the old output show that the triple is acyclic relative to $N$ (`sealTriple_acyclic`); together with acyclicity of the original gates, the append criterion gives acyclicity of the enlarged list (`gatesAcyclic_append`). Its length is $|gs|+3$, and the remaining indices are still below the enlarged endpoint. The induction hypothesis therefore applies to the tail, starting with the enlarged list and output $N+2$.

The resulting list extends the original by the sealing triple followed by the extension supplied by induction. Each gate in the triple is strict (`sealTriple_strict`), and every gate in the later extension is strict by induction. Acyclicity and validity of the final output are supplied by that same induction hypothesis. For each input, the induction hypothesis identifies the final output value with the value at $N+2$ in the enlarged circuit; the sealing-step value-preservation fact identifies that value with the old output value (`vertexValue_sealStep`). This proves the specification.

**Key facts.** `BoolCircuit.gatesAcyclic_append`, `BoolCircuit.sealTriple_acyclic`, `BoolCircuit.sealTriple_strict`, `BoolCircuit.vertexValue_sealStep`.
