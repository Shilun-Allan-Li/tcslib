<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Sizes.inRange_stack -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stack addresses fit the word range

**Claim.** Every stack address $-2j$ with $j$ at most the stack bound lies in the signed word range.

**Proof.** The stack-fit inequality bounds twice the stack bound strictly by $2^W$. Since $j$ is nonnegative and at most the stack bound, this gives $4j<2^W$, which is exactly the required strict upper bound for twice the stack address, $-4j<2^W$. For the lower bound, the same fit inequality gives $4Q<2^W$ and hence $4Q	ext{ }$ is below $2^W$; because $j\le Q$, we have $-2^W\le -4Q\le -4j$. Thus both signed-range inequalities hold.
