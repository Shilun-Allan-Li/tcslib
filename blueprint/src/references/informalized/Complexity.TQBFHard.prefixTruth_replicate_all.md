<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.prefixTruth_replicate_all -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compressing a Universal Quantifier Block

**Claim.** A prefix of $w$ universal quantifiers followed by the remaining prefix is true exactly when every Boolean word of length $w$ makes the remaining prefix true after its block is written into the assignment.

**Proof.** Induct on $w$, allowing the assignment and starting position to vary. When $w=0$, the block is empty, so both sides reduce to truth of the remaining prefix; the only word of length zero is the empty word. For the successor step, the first universal quantifier ranges over a bit $b$, and the induction hypothesis compresses the following $w$ quantifiers into a word $eta$ of length $w$. In the forward direction, any word of length $w+1$ has the form $b::eta$, so the induction hypothesis gives truth after writing $eta$ starting at position $i+1$. Writing this tail after updating position $i$ with $b$ is exactly the same as writing the whole word $b::eta$ starting at $i$ (`writeBlock_update_cons`). Conversely, for each bit $b$, apply the assumed condition to every word $b::eta$; the same identity gives the required assignment for the remaining $w$ universal quantifiers. This proves the equivalence.

**Key facts.** `Complexity.TQBFHard.writeBlock_update_cons`.
