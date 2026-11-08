<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.transduce_head_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output from the Initial False State

**Claim.** For every finite Boolean word $w$, the transducer started in the false state produces the empty word.

**Proof.** Induct on the input word. The empty word produces no output. For a word with head bit $b$ and tail $w'$, the current state is false, so its conjunction with $b$ is false; the output rule therefore emits nothing. The transition remains false, and the induction hypothesis says the remaining input also produces no output. Hence the full output is empty.
