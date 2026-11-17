<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Sizes.inRange_addr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Address values fit the word range

**Claim.** Every address between zero and the space limit has its doubled value in the signed word range.

**Proof.** The lower bound follows because the address is nonnegative, so its double is nonnegative and hence at least $-2^W$. For the upper bound, the address is strictly less than the space limit, so twice the address is less than twice that limit. The size configuration's space-fit inequality bounds twice the space limit by $2^W$; combining these inequalities gives the strict upper bound.
