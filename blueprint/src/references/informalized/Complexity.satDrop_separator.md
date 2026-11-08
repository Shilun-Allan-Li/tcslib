<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satDrop_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recognizing the Separator

**Claim.** Starting in state $0$ at the clamped offset $2|u|$, with a unary counter of length and head position $|u|$ and empty output, the machine reaches after two steps state $3$ at offset $2|u|+2$, with the counter unchanged and its head at $|u|-1$.

**Proof.** The doubled encoding of $u$ has length $2|u|$ (`satBits_length`), so the next two symbols in the pair encoding are the separator bits false and true. The stream-position reading law (`satStreamPos_read`) lets us use these symbols as the machine's input readings. On false in state $0$, the machine advances the input head, leaves the counter head at $|u|$, and enters state $2`; the clamped-position successor law and silent-move action law (`satStreamPos_succ`, `satDrop_move`) give the resulting configuration. On true in state $2$, it advances the input head again, moves the counter head left from $|u|$ to $|u|-1$, and enters state $3$, again without writing or emitting output. Applying the same position and configuration laws gives the stated endpoint.

**Key facts.** `Complexity.satBits_length`, `Complexity.satStreamPos_read`, `Complexity.satStreamPos_succ`, `Complexity.satDrop_move`.
