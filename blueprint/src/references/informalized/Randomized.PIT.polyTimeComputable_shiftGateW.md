<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.polyTimeComputable_shiftGateW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Gate Shifting

**Claim.** For polynomial-time computable functions $f$ and $g$, the function sending $D$ to the shifted gate word formed from $f(D)$ and $g(D)$ is polynomial-time computable.

**Proof.** Compose the first-argument extractor with $g$ to obtain the first argument word, and compose the unary-head extractor with the middle-word operation and then $g$ to obtain the second argument word. The three tag bits of $g(D)$ are polynomial-time computable; prefixing their one-bit outputs with the fixed leading bit gives the header used in the general gate case. In the variable case, the output consists of a fixed four-bit prefix, the first argument word, and a final zero, so it is polynomial-time computable by constant-output and concatenation closure. In the general case, concatenate the header, $f(D)$, the first argument word, a zero, another copy of $f(D)$, the second argument word, and a final zero. Each part is polynomial-time computable, so repeated concatenation gives a polynomial-time function. The proof then combines the variable case and the remaining cases with a conditional on the variable tag, and combines the constant one-gate output with the general case using the one-gate tag test.

**Key facts.** `Randomized.PIT.polyTimeComputable_arg1W`, `Complexity.PolyTimeComputable.comp`, `Randomized.PIT.polyTimeComputable_midW`, `Complexity.BinArith.polyTimeComputable_uHead`, `Randomized.PIT.polyTimeComputable_tagBit`, `Complexity.PolyTimeComputable.append`, `Complexity.polyTimeComputable_prepend`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`, `Randomized.PIT.polyTimeComputable_isVarW`, `Randomized.PIT.polyTimeComputable_isOneW`.
