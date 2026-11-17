<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopDebit_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value Change Under Decrement

**Claim.** For every Boolean word $u$, when the fixed-width decrement reports success, the resulting word's value plus one is the original value; when it reports failure, the original value is zero.

**Proof.** Induct on the word. For the empty word, both the output value and original value are zero, and the operation fails. For a nonempty word, split on its head bit. If the head is true, decrement changes it to false, leaves the tail unchanged, and reports success; the definition of the word value then shows that the output value plus one is the input value. If the head is false, the operation recursively decrements the tail and returns that recursive success flag. Split on the flag. When the recursive operation succeeds, the induction hypothesis gives the value relation for the tail, and the leading zero doubles both tail values, preserving the relation. When it fails, the induction hypothesis says the tail's value is zero; with a leading zero the full word's value is also zero. Thus the stated relation holds in either flag case.
