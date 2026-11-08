<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_incFixed_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Width Increment Preserves Length

**Claim.** Whenever fixed-width increment sends a Boolean word $w$ to $v$, the two words have equal length.

**Proof.** Induct on $w$, allowing the output $v$ to vary. For the empty word, increment returns `none`, so the assumed equality to `some v` is impossible. For a word beginning with `false`, increment changes that first bit to `true` and leaves the tail unchanged; the output is therefore visibly the same length as the input. For a word beginning with `true`, inspect the recursive increment of the tail. If it returns `none`, the whole increment also returns `none`, contradicting the hypothesis. If it returns a word $z$, the induction hypothesis gives $|z|=|w|$ for the tail. The full output is `false :: z`, while the input is `true :: w`, so adding one to both equal tail lengths proves the result.
