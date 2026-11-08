<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGHardFunctions.lean :: BoolCircuit.decodeGate_encodeGate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a gate from its encoding

**Claim.** If a gate has at most two arguments and each argument is less than $S$, decoding its gate code after encoding it recovers the gate exactly.

**Proof.** Write the gate’s argument list by its possible lengths. With no arguments, both encoded argument slots are empty, so filtering the two slots during decoding returns the empty list. With one argument $a$, the bound $a<S$ ensures its encoding is retained as a valid element of $\mathrm{Fin}(S)$, while the second slot is empty; decoding therefore returns $[a]$. With two arguments $a,b$, both bounds ensure both slots survive encoding, and decoding returns $[a,b]$. In all three cases the gate kind is recovered by `decodeKind_encodeKind`, so the decoded gate equals the original. A list of three or more arguments contradicts the hypothesis that its length is at most two.

**Key facts.** `BoolCircuit.decodeKind_encodeKind`.
