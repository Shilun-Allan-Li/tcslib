<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.length_step_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step Bound for Encoded States

**Claim.** Under the live-update length hypothesis, every state string $s$ satisfies the stated upper bound on the length of its successor plus the weighted length of its nested projection.

**Proof.** Replace $g$ by the given step map and divide into its two completed-state branches and its live branch. In either completed-state branch the output is $blockDone$, whose first projection is empty; its length contribution is at most $2$, so the bound follows from the right-hand maximum. In the live branch both relevant first projections are nonempty. The reconstruction property for a nonempty first projection ($eq_pairEncode_of_pairFstD_ne$) therefore expresses $s$ as a nested pair encoding. The encoding length formula ($length_pairEncode$) then writes its length in terms of the two decoded first components and the innermost remainder. The step's output is likewise a nested encoding: its components are the updated string, the old second component with its first bit dropped, and the next-state string. The live-update hypothesis bounds the lengths of the updated and next-state strings. Since the dropped component has length one less than the original nonempty component, the weighted contribution with coefficient $c$ combines with the update bound to fit under the original encoded length plus its corresponding weighted term. This proves the inequality using the left-hand maximum.

**Key facts.** `Complexity.pairFstD_nil`, `Complexity.eq_pairEncode_of_pairFstD_ne`, `Turing.length_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.pairFstD_pairEncode`.
