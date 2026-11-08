<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_arg2W -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second argument field is polynomial-time computable

**Claim.** The function that extracts the second unary-delimited argument field from the body of a word is polynomial-time computable.

**Proof.** The second-field extractor first deletes the four-bit prefix and takes the unary-delimited remainder, then applies the unary head extractor. The remainder extractor `midW` is polynomial-time computable, and so is `uHead` (`polyTimeComputable_uHead`). Closure under composition (`PolyTimeComputable.comp`) therefore gives polynomial-time computability of `arg2W`.

**Key facts.** `Randomized.PIT.polyTimeComputable_midW`, `Complexity.BinArith.polyTimeComputable_uHead`, `Complexity.PolyTimeComputable.comp`.
