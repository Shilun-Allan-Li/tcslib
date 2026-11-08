<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.polyTimeComputable_trLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Transition Loop

**Claim.** The function that applies the transition step repeatedly to an input bit string for its length plus one iterations is polynomial-time computable.

**Proof.** First form the pair encoding whose components are the first projection of the input and the first projection of its second projection. These projections and the pair encoding are polynomial-time computable. From this encoded pair, the length-based prefix used by the trial test is polynomial-time computable, as are the trial test itself and the conjunction of that test with the acceptance bit. The transition step then re-encodes the original first projection, the dropped-prefix data, and this one-bit conjunction; projection, composition, and pair-encoding closure show that the step is polynomial-time computable. For the iteration bound, the transition preserves the first projection of the configuration, and its length increases by at most a fixed constant times one plus the length of that projection. The bound for repeated transitions with fixed context therefore gives a quadratic bound in the initial encoded length. The polynomial-time loop theorem applies with this bound, yielding polynomial-time computability of the for-loop.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.BinArith.polyTimeComputable_slot2`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_app`, `Randomized.polyTimeComputable_takePrefixByLen`, `Randomized.PIT.polyTimeComputable_trialTest`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.polyTimeComputable_headD`, `Complexity.BinArith.polyTimeComputable_test_app`, `Complexity.polyTimeComputable_and`, `Randomized.polyTimeComputable_dropPrefixByLen`, `Complexity.PolyTimeComputable.comp`, `Complexity.length_pair_components_le`, `Complexity.BinArith.forLoop_bound_of_ctx`, `Complexity.BinArith.polyTimeComputable_forLoop`.
