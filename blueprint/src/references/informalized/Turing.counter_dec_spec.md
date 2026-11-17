<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_dec_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Decrement Specification

**Claim.** For every Boolean word $w$, if decrement is undefined then $w$ consists entirely of false entries. If decrement returns $v$, then $v$ has the same length as $w$, its binary value is one less, and its number of true entries is determined by the number of true entries in $w$ and the length of the initial run of false entries.

**Proof.** Proceed by induction on $w$. The empty word has undefined decrement and is the empty all-false word. If $w$ begins with true, decrement changes that first entry to false and leaves the rest unchanged. The lengths therefore agree, the binary value drops by one, and the number of true entries drops by one; these are the claimed formulas since the initial run of false entries is empty. If $w$ begins with false, inspect the decrement of its tail. When that decrement is undefined, the induction hypothesis says the tail is all false, so the whole word is all false and decrement is undefined. When it returns a word $v$, the induction hypothesis gives the length, binary-value, and true-count relations for the tail and $v$. Decrement prefixes a true to $v$; the binary-value recurrence for a leading digit and the fact that the leading false extends the initial false run by one give the stated relations for the whole word.
