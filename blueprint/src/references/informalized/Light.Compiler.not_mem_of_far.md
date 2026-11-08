<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/WholeProgram.lean :: Light.Compiler.not_mem_of_far -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Addresses Outside Reserved Regions

**Claim.** Assume the word size fits the limits, pool bound, and stack size specified for $P$ and $d$. Any address $a$ lying below the negative low-cell bound or at least the space limit belongs to none of the listed constant, frame, writable, result, or difference-register address regions.

**Proof.** The proof first uses the bound that the main frame and all frames fit within the stack allocation (`frame_le_stackCells`). It also uses the lower bound on the dispatcher position in terms of frame size (`two_mul_frameSize_add_le_dispPos`). By the definition of the low-cell bound as the maximum of twice the stack-cell count and the pool-address bound, both quantities are at most that bound. Unfolding the definitions of the writable set and the generated layout, it remains to check the two alternatives in the hypothesis: an address below the negative low-cell bound is too small to lie in any of the reserved negative-address regions, while an address at least the space limit is outside both those regions and the writable set's nonnegative addresses, which are strictly below that limit. These bounds exclude each component of the stated union.

**Key facts.** `Light.Compiler.frame_le_stackCells`, `Light.Compiler.two_mul_frameSize_add_le_dispPos`.

**Caveat.** The source ends the exclusion argument with the custom `cells` tactic, whose detailed arithmetic and region-by-region cases are not given in the supplied upstream statements; the explanation summarizes the intended range-exclusion argument.
