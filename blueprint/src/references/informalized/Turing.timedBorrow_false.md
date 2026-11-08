<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedBorrow_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrowing Zero Leaves the Word Unchanged

**Claim.** Subtracting an incoming borrow flag set to false returns a false final borrow flag and leaves every Boolean word unchanged.

**Proof.** Induct on the word. For the empty word, the recursion returns the incoming flag and the empty word, so the claim follows immediately. For a word with first bit $b$ and tail $bs$, the induction hypothesis says that processing $bs$ with a false carry returns $(\mathrm{false},bs)$. Since the incoming carry is false, the recursive carry passed to the tail is also false, and the first output bit is $b\mathbin{\mathrm{xor}}\mathrm{false}=b$. Thus the whole result is $(\mathrm{false},b::bs)$.
