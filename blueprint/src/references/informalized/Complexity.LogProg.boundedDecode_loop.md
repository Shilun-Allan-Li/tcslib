<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.boundedDecode_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Decoding Loop

**Claim.** Under the stated program, register, suffix-bound, initial-value, and oracle hypotheses, the decoding loop reaches the done state with the pointer at the base, the accumulator equal to the value of the whole word, the temporary register zero, all registers bounded by $B$, and all other registers unchanged; every prior configuration satisfies the safety conditions and the same bound.

**Proof.** Apply the stride-loop result (`boundedDecodeStride_loop`) with stride $1$. Its test instruction is the given comparison followed by the single down state; the only down transition is exactly the specified pointer decrement, and the next state is the read state. The pointer and oracle hypotheses for stride $1$ are the hypotheses here, since $1\cdot k=k$ and $1\cdot i=i$. The positive-stride condition also holds. The stride-loop conclusion therefore gives the required final register values and safe bounded execution.

**Key facts.** `Complexity.LogProg.boundedDecodeStride_loop`.
