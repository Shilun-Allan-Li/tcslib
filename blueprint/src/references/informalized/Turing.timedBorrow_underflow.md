<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedBorrow_underflow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Underflow Criterion

**Claim.** Starting with an incoming borrow flag set to true, the final borrow flag is true exactly when the Boolean word has little-endian value zero.

**Proof.** Induct on the word. The empty word has value zero, and processing it with an incoming true borrow leaves the final borrow true. For a word $b::bs$, split on its first bit. If $b$ is false, the recursive call processes the tail with a true carry, so the induction hypothesis says its final carry is true exactly when the tail has value zero. The current word's value is twice the tail's value, so this is precisely the desired criterion. If $b$ is true, the recursive carry passed to the tail is false. The zero-incoming-borrow result (`timedBorrow_false`) says that processing the tail then leaves a false final carry, while the current word has value $2\,\mathrm{timedValue}(bs)+1$, which is nonzero. Thus both sides of the equivalence are false in this case.

**Key facts.** `Turing.timedBorrow_false`.
