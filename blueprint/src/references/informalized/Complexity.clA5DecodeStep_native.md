<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5DecodeStep_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Decoding Step

**Claim.** The function that sends each binary word to its one-step bounded-decoding state is polynomial-time computable.

**Proof.** Extract the first header field as $w$, and form $u$ by appending one true bit to the second header field. The header-field extraction is polynomial-time computable, as is appending a fixed word (`clHeaderField_native`, `clNative_append`, `clA5_pt_const`). The length of $u$ is polynomial-time computable: the length function is linear-time computable, and $u$ itself is polynomial-time computable (`clNative_linear`, `Turing.FinTM.computesFunInTime_lengthBits`). Next compute the one-bit result that tests whether the binary value of $w$ equals the length of $u$ (`clA5EqNum_native`). The identity that a natural number is the value of its binary bit list (`clNum_bits`) identifies the number represented by the length computation used in this test. Use that test to choose between $u$ and the second header tail, a choice of polynomial-time computable functions (`clA5_pt_cond`, `clHeaderTail_native`). Finally, pair-encode $w$ with the pair-encoding of $u$ and the selected tail; pair-encoding polynomial-time computable functions preserves polynomial-time computability (`clNative_pair`). This is exactly the specified one-step decoding state.

**Key facts.** `Complexity.clHeaderField_native`, `Complexity.clNative_append`, `Complexity.clA5_pt_const`, `Complexity.clNative_linear`, `Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.clA5EqNum_native`, `Complexity.clNum_bits`, `Complexity.clA5_pt_cond`, `Complexity.clHeaderTail_native`, `Complexity.clNative_pair`.
