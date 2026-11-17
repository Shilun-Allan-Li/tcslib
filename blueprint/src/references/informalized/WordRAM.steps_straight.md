<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.steps_straight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a straight code segment

**Claim.** If a list of straight instructions is a prefix of the program at $pc$, then executing its length from memory $m$ advances the program counter by that length and produces the successive effects of the instructions.

**Proof.** Proceed by induction on the instruction list. For the empty list, zero steps leave the configuration unchanged, and the empty fold of effects leaves the memory unchanged. For a nonempty list with first instruction $i$ and tail $l$, the hypotheses give that $i$ is straight and that it is the instruction at the current program position: the prefix facts `WordRAM.CodeAt.head` and `WordRAM.CodeAt.tail` identify the head and leave the tail as a prefix at the next position. The one-step straight-instruction rule (`WordRAM.step_straight`) advances the counter by one and changes memory to the effect of $i$. Apply the induction hypothesis to $l$, starting from that new position and memory, to execute the remaining instructions. The resulting memory is the fold of effects for the whole list, and the final position is $pc+1+|l|=pc+|i::l|$; `WordRAM.Steps.cast_pos` aligns this arithmetic expression with the stated endpoint.

**Key facts.** `WordRAM.CodeAt.head`, `WordRAM.step_straight`, `WordRAM.CodeAt.tail`, `WordRAM.Steps.cast_pos`.
