<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.evalModW_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of Modular Circuit Evaluation

**Claim.** For a nonempty, well-formed arithmetic circuit, the encoded evaluator outputs a bit string whose binary value is less than $b(R)+1$, and whose residue modulo $b(R)+1$ equals the circuit’s value over $\mathbb{Z}/(b(R)+1)\mathbb{Z}$ at the inputs represented by $P$.

**Proof.** Set $k=b(R)+1$, which is positive. The gate-run correctness theorem identifies the evaluator state for the encoded circuit with the state encoding the list of successive gate values, computed modulo $k$ at the inputs $ptVal(P)$ ($\mathrm{gateRun\_encodeGates}$). The binary-value theorem for bit encodings converts the evaluator’s final bit string into the corresponding natural number ($\mathrm{bitsVal\_bits}$), and the formula for reading a value from an encoded state reduces this number to the final entry of the computed-value list ($\mathrm{runVal\_encState}$).

Because the circuit is nonempty, that final entry is at index $|C.gates|-1$. If it is present, it occurs in the list of computed gate values; every such value is less than $k$ ($\mathrm{lt\_of\_mem\_evalVals}$), proving the strict bound. If the indexed entry is absent, the default value is zero, also less than positive $k$. For the residue identity, the natural-number values of the gates, cast into $\mathbb{Z}/k\mathbb{Z}$, agree entry by entry with running the circuit over that ring ($\mathrm{natCast\_evalVals}$). Casting the final list entry commutes with taking that entry ($\mathrm{getD\_map\_natCast}$), so the evaluator’s residue is precisely the circuit’s output. The nonemptiness and well-formedness hypotheses ensure that this final entry is the circuit output and that each gate uses only earlier gates.

**Key facts.** `Randomized.PIT.gateRun_encodeGates`, `Complexity.LogProg.bitsVal_bits`, `Randomized.PIT.runVal_encState`, `Randomized.PIT.lt_of_mem_evalVals`, `Randomized.PIT.natCast_evalVals`, `Randomized.PIT.getD_map_natCast`.
