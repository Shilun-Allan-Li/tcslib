<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: Language.InStrictSIZE.inSIZE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict size classes lie in size classes

**Claim.** A language recognized by a strict circuit family with size at most $T(n)$ is recognized by a well-formed fan-in-two family with the same size bound.

**Proof.** Use the family witnessing strict size membership. At input length zero, its circuit already has fan-in at most two by hypothesis. At each positive length, strictness implies fan-in at most two (`BoolCircuit.DAGCircuit.IsStrict.isFaninTwo`). Thus the whole family has fan-in at most two at every length. Its size bound and recognized language are unchanged, giving membership in the ordinary size class.

**Key facts.** `BoolCircuit.DAGCircuit.IsStrict.isFaninTwo`.
