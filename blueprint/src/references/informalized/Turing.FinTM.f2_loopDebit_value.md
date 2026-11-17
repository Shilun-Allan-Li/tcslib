<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopDebit_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value After a Loop Debit

**Claim.** For every Boolean word $u$, after applying the loop debit, a true flag means the new word's value plus one equals the original value, while a false flag means the original value is zero.

**Proof.** Proceed by induction on the word. For the empty word, the debit returns the empty word with a false flag, and both the asserted zero value and the recursive definition of value give zero. For a word beginning with true, the debit changes its first bit to false and returns a true flag. The recursive value formula shows that this removes exactly the leading contribution of one, so the new word's value plus one is the original value. For a word beginning with false, the debit changes that bit to true and continues on the tail. Split on the flag returned from the tail and apply the induction hypothesis. If the tail flag is true, the tail value is the debited tail's value plus one; substituting into the recursive value formulas gives the required relation for the whole word. If the tail flag is false, the tail value is zero, so the original word's value is also zero. These are precisely the two alternatives asserted for the resulting flag.
