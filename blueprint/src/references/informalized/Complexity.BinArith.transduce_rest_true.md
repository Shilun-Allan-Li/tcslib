<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.transduce_rest_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output from the Initial True State

**Claim.** For every finite Boolean word $w$, the transducer started in the true state outputs exactly $w$.

**Proof.** Induct on the input word. The empty word is output as empty. If the input begins with $b$ and has tail $w'$, the current state is true, so the output rule emits $b$. The transition from this state is true regardless of $b$, since it is the disjunction of true with the negation of $b$. By the induction hypothesis, the tail is therefore output unchanged. Together these outputs form the original word.
