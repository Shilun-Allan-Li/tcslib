<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.polyTimeComputable_sampleStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Sampling Step

**Claim.** The sampling-step function, which splits the encoded sample using the encoded state parameter and updates the state and sample according to the stated test and binary-value rule, is polynomial-time computable.

**Proof.** Extract the outer first component and then its two nested components; each extraction is polynomial-time computable. Pair the sample component with the parameter component. The prefix-taking procedure applied to this pair gives the requested prefix, and the corresponding suffix-dropping procedure gives the remaining sample. For the update condition, test whether the nested sample is empty and whether the prefix's binary value is less than the nested state value; both tests are polynomial-time computable, and their conjunction is as well. In the successful case, normalize the prefix's binary value and prepend the fixed leading bit; concatenation closure gives a polynomial-time construction. In the other case, retain the nested sample. The conditional closure theorem combines these alternatives. Finally, pair the extracted state with the suffix and the selected updated sample in the prescribed nested encoding; polynomial-time pair encoding yields the stated sampling step.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.BinArith.polyTimeComputable_slot2`, `Complexity.PolyTimeComputable.pairEncode`, `Randomized.polyTimeComputable_takePrefixByLen`, `Complexity.polyTimeComputable_isNil`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.BinArith.polyTimeComputable_lt`, `Complexity.polyTimeComputable_and`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.append`, `Complexity.BinArith.polyTimeComputable_normBits`, `Randomized.polyTimeComputable_dropPrefixByLen`, `Complexity.polyTimeComputable_ite`.
