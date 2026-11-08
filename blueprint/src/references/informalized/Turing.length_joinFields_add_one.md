<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.length_joinFields_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of joined fields

**Claim.** For a nonempty finite list of finite fields, the length of the fields joined by one separator between consecutive fields, plus one, equals the sum of each field's length plus one.

**Proof.** Induct on the list of fields. The empty case is impossible under the nonemptiness hypothesis. For a singleton field $u$, joining gives $u$ itself, and the offset is $|u|+1$, so the equality follows. For at least two fields, write the list as $u::v::fs$. The join is $u$ followed by one separator and then the join of $v::fs$ (`joinFields_cons_cons`). By induction, the latter join's length plus one is the offset for $v::fs$. The offset formula says the full offset is $|u|+1$ plus that tail offset (`fieldOffset_cons_succ`). Substituting these expressions into the length of the concatenation and simplifying the natural-number arithmetic proves the result.

**Key facts.** `Turing.joinFields_cons_cons`, `Turing.fieldOffset_cons_succ`.
