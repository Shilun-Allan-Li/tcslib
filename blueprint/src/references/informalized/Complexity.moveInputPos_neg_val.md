<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.moveInputPos_neg_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Position After a Negative Move

**Claim.** For a valid head position $q$ among the $n+2$ positions, moving in the negative direction produces the natural-number position $q-1$, with natural subtraction.

**Proof.** Represent the position by its natural-number value $q$, where $q<n+2$. A negative move adds $-1$ in the integers, then converts the result to a natural number. If $q>0$, this is $q-1$. If $q=0$, the integer result is $-1$, whose natural-number conversion is $0$; this agrees with natural subtraction $0-1=0$. The resulting position is within the allowed range, so the move's boundary fallback is not needed.
