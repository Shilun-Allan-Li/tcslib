<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedBorrow_fold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Subtraction as a Left-to-Right Fold

**Claim.** Sweeping a Boolean word from left to right with the stated carry and output-bit rule produces exactly the same final carry and output word as fixed-width borrow subtraction.

**Proof.** Induct on the word, generalizing the incoming carry. For the empty word, both procedures return the incoming carry together with the empty output. For a word $b::bs$, the fold first updates the carry to $carry\wedge\lnot b$ and emits $b\oplus carry$. It then sweeps the tail using that updated carry. By the induction hypothesis, this tail sweep agrees with the recursive tail computation in fixed-width borrow subtraction. Both procedures therefore have the same final carry and the same output, beginning with $b\oplus carry$.
