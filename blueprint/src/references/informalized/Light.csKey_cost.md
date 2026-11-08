<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.csKey_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of the key expression

**Claim.** The expression used to load an item's key in counting sort has cost $11$.

**Proof.** Expand the key expression into its nested address calculations and memory loads, and evaluate cost recursively: a variable or constant has cost $1$, an operation has cost one more than the costs of its two operands, and a load has cost one more than the cost of its address. This gives total cost $11$.
