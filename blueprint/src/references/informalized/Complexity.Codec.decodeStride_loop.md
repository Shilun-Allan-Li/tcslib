<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Engine.lean :: Complexity.Codec.decodeStride_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stride-Based Decoding Loop

**Claim.** Under the specified loop instructions, register bounds, initial values, suffix-value bounds, and oracle answers, there is a bounded final register assignment with the pointer reset to its base, the accumulator equal to the binary value of $w$, and the temporary register zero; every other register is unchanged. The program reaches the done label through a finite guarded execution.

**Proof.** The hypotheses give exactly the instruction equations and register conditions required by `boundedDecodeStride_loop`: the test and stride-length decrement chain position the pointer, the read queries the bit indexed by that pointer, and the copy/bump and clear/scale/take/increment/add instructions process the queried bit while rebuilding the accumulator. The assumed oracle answers supply the required bit at every index, while the suffix-value hypotheses provide the bounds used throughout the loop. Applying `boundedDecodeStride_loop` yields a final assignment satisfying the stated register values, frame property, bound, and guarded reachability.

**Key facts.** `Complexity.LogProg.boundedDecodeStride_loop`.
