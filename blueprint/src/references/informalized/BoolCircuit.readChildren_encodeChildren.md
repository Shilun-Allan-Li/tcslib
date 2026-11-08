<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.readChildren_encodeChildren -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding a List of Child Circuits

**Claim.** If every child circuit can be recovered from its encoding whenever the fuel is at least the encoding length, then a child-list encoding whose length is within the available fuel decodes to exactly that list and leaves the appended remainder unchanged.

**Proof.** Induct on the child list. For the empty list, its encoding is the single terminating false bit. The fuel cannot be zero because the encoding has positive length; with positive fuel, the reader sees the terminator and returns the empty list with the remainder untouched.

For a nonempty list $d::ds$, its encoding starts with a true marker, followed by the encoding of $d$ and then the encoding of $ds$ (`encodeChildren_cons`). Positive total encoding length again rules out zero fuel. With fuel $f+1$, the reader consumes the marker and reads $d$ from its encoding followed by the encoded tail and remainder. The hypothesis for $d$ applies because its encoding length is at most $f$. It returns $d$ and leaves precisely the encoded tail and remainder. The induction hypothesis applies to that tail, whose encoding also fits within $f$, and returns $ds$ with the original remainder untouched. Combining these readings gives the required result for $d::ds$.

**Key facts.** `BoolCircuit.encodeChildren_nil`, `BoolCircuit.encodeChildren_cons`.
