<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.encodeList_eq_flatMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List encoding by concatenation

**Claim.** Encoding a finite list by prefixing each element's encoding with one and terminating the list with zero yields the concatenation of those prefixed encodings in list order, followed by zero.

**Proof.** Induct on the list. For the empty list, both sides are the single terminating zero. For a list with head $a$ and tail $l$, the recursive encoding is one followed by $f(a)$ and then the encoding of $l$. By the induction hypothesis, that tail encoding is the concatenation of the prefixed encodings for $l$, followed by zero. Joining these pieces gives exactly the claimed concatenation.
