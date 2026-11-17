<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.T_gates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dualization of Encoded Gates

**Claim.** For every finite list of gates $G$ and every finite bit string $r$, processing the encoding of $G$ followed by $r$ from state $g$ yields the encoding of the list obtained by replacing each gate with its dual, followed by the unchanged suffix $r$.

**Proof.** Induct on the list of gates. For the empty list, the encoding is the terminating bit $0$; from state $g$ this moves the transducer to state $o$, which copies the remaining suffix unchanged. For a nonempty list, write its first gate as its kind and argument list. The two encoded kind bits are handled directly: an AND kind becomes OR, an OR kind becomes AND, and a NOT kind stays unchanged. The transducer then reaches the argument-reading state. The argument-processing fact (`T_args`) says that the encoded arguments are preserved and the remaining input is processed from state $g$. Apply the induction hypothesis to the remaining encoded gates and suffix. Thus the first gate is replaced by its dual and the rest of the encoding is dualized, while the suffix is copied unchanged.

**Key facts.** `BoolCircuit.CktSatReduction.T_cons`, `BoolCircuit.CktSatReduction.T_o`, `BoolCircuit.CktSatReduction.T_args`.
