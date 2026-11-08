<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.UHALT_mem_PPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Halting Has Polynomial Circuit Size

**Claim.** For every machine representation scheme $c$, the unary language of numbers whose binary expansions begin with $1s$, where $s$ encodes an advice string and an input on which the machine decoded from that advice halts, has Boolean circuits of fan-in at most two and size bounded by a polynomial in the input length.

**Proof.** The general theorem `Language.unary_inPPoly` says that every unary language has polynomial-size Boolean circuits of fan-in at most two. Since `UHALT c` is defined as a unary language, applying that theorem directly gives the claimed circuit bound.

**Key facts.** `Language.unary_inPPoly`.
