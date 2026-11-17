<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardFunctions.lean :: BoolCircuit.card_computable_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Functions Computed by Small Tree Circuits

**Claim.** The number of Boolean functions on $n$ variables computed by Boolean circuit trees of size at most $S$ is at most $2^{(n+4)S}$.

**Proof.** Choose, for each function represented by a tree of size at most $S$, one such tree. Map the function to the natural number obtained by encoding that tree as a bit list and interpreting the list as a binary number. This map is injective: equality of the numbers implies equality of the bit lists ( `BoolCircuit.bitsToNat_injective`), and equality of the encoding lists implies equality of the trees ( `BoolCircuit.encodeCircuit_injective`). For a tree $C$, its code number is less than $2^{	ext{length of code}+1}$ ( `BoolCircuit.bitsToNat_lt`). The code-length estimate ( `BoolCircuit.length_encodeCircuit_succ_le`) and the size bound show that this is at most $2^{(n+4)S}$. Thus the chosen functions inject into a set of that many natural numbers, yielding the claimed cardinality bound.

**Key facts.** `BoolCircuit.bitsToNat_injective`, `BoolCircuit.encodeCircuit_injective`, `BoolCircuit.bitsToNat_lt`, `BoolCircuit.length_encodeCircuit_succ_le`.
