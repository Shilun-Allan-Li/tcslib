<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Dispatcher.lean :: Light.Compiler.length_dispatcher -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatcher Length

**Claim.** For every $n\in\mathbb N$, the dispatcher built from $n$ entries has length $2n$.

**Proof.** The dispatcher is formed by mapping each index in the range from $0$ to $n-1$ to a pair of instructions. A flat map has length equal to the sum of the lengths of the mapped lists; each pair has length two. There are $n$ indices, so the total is $2n$.
