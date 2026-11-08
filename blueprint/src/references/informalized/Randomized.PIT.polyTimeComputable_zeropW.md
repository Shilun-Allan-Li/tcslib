<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.polyTimeComputable_zeropW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Zero Predicate

**Claim.** The Boolean function that returns the zero-predicate result on a bit string as a one-bit string is computable in polynomial time.

**Proof.** First compute whether the first decoded component is valid; this is polynomial-time computable by composing the validity test with first-component extraction. Separately, form the input to the pipeline test: extract the first component, compute its unary head and unary remainder, compute the index component of its scan run, and assemble these fields with the second decoded component using pair encodings and a constant empty string. Each extraction and component procedure is polynomial-time computable, so the assembled string is too. Apply the pipeline predicate to this string and negate its one-bit result. The zero predicate is the disjunction of failure of the validity test and this negated pipeline result. Polynomial-time negation and disjunction therefore give the claimed computation.

**Key facts.** `Complexity.BinArith.polyTimeComputable_test_app`, `Randomized.PIT.polyTimeComputable_validW`, `Complexity.PolyTimeComputable.comp`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.BinArith.polyTimeComputable_app`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_uHead`, `Complexity.BinArith.polyTimeComputable_uRest`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_pairSndD`, `Randomized.PIT.polyTimeComputable_scanRun`, `Randomized.PIT.polyTimeComputable_pipe`, `Complexity.polyTimeComputable_not`, `Complexity.polyTimeComputable_or`.
