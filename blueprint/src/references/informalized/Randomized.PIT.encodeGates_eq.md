<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.encodeGates_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding a List of Algebraic Gates

**Claim.** For any list of algebraic gates $g_1,\ldots,g_m$, its encoding is the concatenation of a marker bit $1$ followed by each gate’s encoding in order, and a final marker bit $0$.

**Proof.** Induct on the gate list. For the empty list, the encoding is the single terminating bit $0$, while the concatenation of no gate blocks followed by $0$ is also $[0]$. For a list with head gate $g$ and tail $gs$, the recursive encoding is $1$ followed by the encoding of $g$ and then the encoding of $gs$. By the induction hypothesis, the latter is the concatenation of the tail’s marked gate blocks and the final $0$. This is exactly the head block $1$ followed by $g$’s encoding, then all tail blocks and the terminator.
