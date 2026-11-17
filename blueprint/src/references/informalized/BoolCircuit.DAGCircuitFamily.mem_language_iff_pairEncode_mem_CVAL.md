<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PUniformP.lean :: BoolCircuit.DAGCircuitFamily.mem_language_iff_pairEncode_mem_CVAL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit language and circuit value

**Claim.** If every circuit in the family has fan-in at most two, no repeated gate arguments, and exactly one argument at every NOT gate, then the family accepts $x$ if and only if the encoding of its circuit for inputs of length $|x|$, paired with $x$, belongs to the circuit value language.

**Proof.** If the family accepts $x$, choose $x$ and its circuit of input length $|x|$ as witnesses in the definition of the circuit value language. The fan-in-two hypothesis supplies the required circuit well-formedness, and acceptance supplies its true output. Conversely, membership in the circuit value language gives a word $y$ and a circuit $D$ whose encoding paired with $y$ is the specified encoding, with $D$ well-formed and evaluating to true on $y$. Injectivity of the pairing identifies $y=x$ and the circuit encodings (pairEncode_injective). Injectivity of circuit encoding then identifies $D$ with the family circuit for inputs of length $|x|$ (DAGCircuit.encode_injective). Its true evaluation therefore says that the family accepts $x$, by the membership characterization for the family language (DAGCircuitFamily.mem_language_iff).

**Key facts.** `Turing.pairEncode_injective`, `BoolCircuit.DAGCircuit.encode_injective`, `BoolCircuit.DAGCircuitFamily.mem_language_iff`.
