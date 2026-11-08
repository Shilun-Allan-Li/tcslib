<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.fT_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transduction of a paired word

**Claim.** Applying the specified one-pass transduction to the paired encoding of two Boolean words yields the bit code of the first word, followed by the separator 00 and then the second word.

**Proof.** Induct on the first word. If it is empty, its paired encoding is just the separator 01 followed by the second word. The transducer processes the separator to produce 00, then copies the remaining word; the copying property for the transducer started in its initial copying state is exactly transduce_fT_copy. This gives the claimed output in the base case. For a nonempty word with first bit $b$ and tail $w$, the encoding begins with the two copies of $b$, followed by the encoding of $w$, the separator, and the second word. The transition rules process this doubled bit to emit $b1$ and return the transducer to the state in which the induction hypothesis applies to the rest. Applying that hypothesis produces the code of $w$, then 00 and the second word. Concatenating the initial $b1$ gives the code of the entire first word, followed by the required suffix.

**Key facts.** `Complexity.Meyer.transduce_fT_copy`.
