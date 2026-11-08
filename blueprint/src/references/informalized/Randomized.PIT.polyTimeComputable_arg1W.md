<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_arg1W -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First argument field is polynomial-time computable

**Claim.** The function that extracts the first unary-delimited argument field from the body of a word is polynomial-time computable.

**Proof.** The extraction is the composition of deleting the first four bits and then applying the unary-field head extractor. Deleting a fixed prefix is polynomial-time computable (`polyTimeComputable_bodyW`), and the unary head extractor is polynomial-time computable (`polyTimeComputable_uHead`). Polynomial-time computability is closed under composition (`PolyTimeComputable.comp`), so their composition, which is `arg1W`, is polynomial-time computable.

**Key facts.** `Randomized.PIT.polyTimeComputable_bodyW`, `Complexity.BinArith.polyTimeComputable_uHead`, `Complexity.PolyTimeComputable.comp`.
