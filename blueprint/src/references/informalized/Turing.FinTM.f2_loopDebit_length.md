<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopDebit_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Preservation by the Loop Debit

**Claim.** For every finite Boolean list $u$, the list component of the F2 loop debit applied to $u$ has the same length as $u$.

**Proof.** Proceed by induction on $u$. The empty list is handled directly. For a nonempty list, split on its first Boolean symbol. If it is true, the debit changes that symbol to false and leaves the tail unchanged, so the length is preserved. If it is false, the debit changes that symbol to true and recursively debits the tail; the induction hypothesis says the tail's length is preserved, and adding the unchanged single head position preserves the total length.
