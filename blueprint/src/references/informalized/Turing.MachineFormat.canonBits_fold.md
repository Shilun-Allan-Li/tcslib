<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonBits_fold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Fold and Final Symbol

**Claim.** Folding a Boolean word from left to right with the operation that replaces the accumulator by the current symbol returns the word’s last symbol, or the initial value when the word is empty.

**Proof.** Induct on the word, allowing the initial value to vary. For the empty word, both sides are the initial value. For a word with first symbol $b$ and tail $w$, the fold first replaces the initial value by $b$, then folds the tail. By the induction hypothesis, this is the last symbol of $w$ when the tail is nonempty, and is $b$ when the tail is empty. This is exactly the last-symbol-with-default description of the whole word.
