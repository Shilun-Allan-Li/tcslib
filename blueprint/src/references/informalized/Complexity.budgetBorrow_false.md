<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.budgetBorrow_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Pass with No Incoming Borrow

**Claim.** For every finite bit word, a borrow pass started with a false borrow flag returns a false final flag and leaves the word unchanged.

**Proof.** Induct on the word. For the empty word, the pass returns the incoming false flag and the empty word. For a word beginning with bit $b$, the recursive pass receives carry $\text{false}\mathbin{\&\&}\neg b=\text{false}$ on the tail. By induction it returns false and leaves that tail unchanged. The current output bit is $b\mathbin{\mathrm{xor}}\text{false}=b$, so the whole word is unchanged and the final flag is false.
