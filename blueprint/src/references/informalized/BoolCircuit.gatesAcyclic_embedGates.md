<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.gatesAcyclic_embedGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of an embedded circuit

**Claim.** Embedding a circuit $D$ using a source list of length $m$ with entries below $L$, then appending a gate that reads the embedded output, yields a list acyclic from $L$.

**Proof.** First consider the remapped list corresponding to the gates of $D$. At position $i$, any input in the deduplicated remapped argument list comes from an original input $b$ of the gate at position $i$. The circuit's acyclicity gives $b<m+i$, and the embedding bound (\texttt{embedMap_lt}) then gives that its remapped index is below $L+i$. Thus the remapped gate list is acyclic from $L$. The final gate reads only the embedded output. Since the circuit output is below $m+|D.\mathrm{gates}|$, the same embedding bound places this input below $L+|D.\mathrm{gates}|$, the bound at the appended position. Appending a gate whose inputs satisfy that bound preserves acyclicity (\texttt{GatesAcyclic.snoc}).

**Key facts.** `BoolCircuit.embedMap_lt`, `BoolCircuit.GatesAcyclic.snoc`.
