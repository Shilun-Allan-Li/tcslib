<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.polyTimeComputable_uniformSampleAlg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Uniform Sampling

**Claim.** The function that initializes the encoded sampling state from the decoded input and iterates the sampling step for the encoded number of rounds is polynomial-time computable; its output is the final sample component of the resulting state.

**Proof.** 1. The iteration theorem for polynomial-time functions applies to the sampling step once its iterates have a polynomial length bound. The step preserves the first decoded state component. Its output length is bounded by the current state length plus a fixed multiple of the length of that component plus one: decoded pair components do not exceed the input length, prefix and suffix operations do not increase length, and the binary representation of a natural number has length at most the input representation from which its value was computed (Complexity.length_pair_components_le, Complexity.length_pairSndD_le, and BinArith.length_bits_bitsVal_le). Pair encoding adds length according to $2|x|+2+|y|$ (Turing.length_pairEncode); considering the two branches of the step gives the required one-step bound. The iteration bound for a context-preserving step (Complexity.BinArith.forLoop_bound_of_ctx) therefore supplies a polynomial bound on all iterates up to the encoded loop count. The polynomial-time iteration theorem (Complexity.BinArith.polyTimeComputable_forLoop), together with polynomial-time computability of the sampling step, shows that running the loop is polynomial-time computable.

2. The initial state is built from decoded components, a subtraction on decoded data, and fixed empty or singleton strings, with these pieces combined by pair encodings. Decoding, subtraction, constant functions, composition, and pairing are all polynomial-time computable (including Complexity.BinArith.polyTimeComputable_sub and the stated pair-encoding and composition results), so the initialization is polynomial-time computable.

3. Compose initialization with the loop, then project out the fourth nested pair's second component. This projection is polynomial-time computable (Complexity.BinArith.polyTimeComputable_slot4), and the resulting function is exactly the final sample component specified in the claim.

**Key facts.** `Randomized.polyTimeComputable_sampleStep`, `Complexity.length_pair_components_le`, `Complexity.length_pairSndD_le`, `Complexity.BinArith.length_bits_bitsVal_le`, `Turing.length_pairEncode`, `Complexity.BinArith.forLoop_bound_of_ctx`, `Complexity.BinArith.polyTimeComputable_forLoop`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.BinArith.polyTimeComputable_sub`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.PolyTimeComputable.comp`, `Complexity.BinArith.polyTimeComputable_slot4`.
