<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedBorrow_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Subtraction Preserves Length

**Claim.** For every incoming borrow flag and Boolean word, the output word has the same length as the input word.

**Proof.** Induct on the word, generalizing the incoming carry. The empty word produces an empty output, so the lengths agree. For $b::bs$, the recursion emits one output bit and then processes the tail. By the induction hypothesis, the tail output has length $|bs|$; hence the full output has length $1+|bs|$, which is the length of the input word.
