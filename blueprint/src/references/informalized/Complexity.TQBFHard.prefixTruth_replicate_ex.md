<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.prefixTruth_replicate_ex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compressing an Existential Quantifier Block

**Claim.** A prefix of $w$ existential quantifiers followed by the remaining prefix is true exactly when there is a Boolean word of length $w$ making the remaining prefix true after its block is written into the assignment.

**Proof.** Induct on $w$, allowing the assignment and starting position to vary. At $w=0$, the empty word is the sole word of length zero, and writing it changes nothing, so the two statements agree. For the successor step, the first existential quantifier supplies a bit $b$. By induction, the remaining $w$ existential quantifiers supply a word $\beta$ of length $w$; together they form the word $b::\beta$ of length $w+1$. Writing the tail after updating position $i$ with $b$ agrees with writing the full word at position $i$ (`writeBlock_update_cons`), giving the desired witness. Conversely, any witness word of length $w+1$ decomposes as $b::\beta$; its head supplies the first existential choice, and the induction hypothesis applied to its tail supplies the remaining choices. The same block-writing identity matches the resulting assignment.

**Key facts.** `Complexity.TQBFHard.writeBlock_update_cons`.
