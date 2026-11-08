<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.fieldsTape_no_double_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No adjacent blank cells between fields

**Claim.** If all fields are nonempty, then within the specified range the joined-fields tape cannot be blank at both consecutive positions $z$ and $z+1$.

**Proof.** Induct on the list of fields. The empty list has no position satisfying the strict endpoint bound. For a nonempty list, its first field $u$ is nonempty. If $z<|u|$, then $z$ lies within that field, and the field-content identity (`Turing.fieldsTape_field`) says the tape there contains a symbol, contradicting blankness. If the list has no further fields, the endpoint bound rules out the remaining positions.

Otherwise write the list as $u::v::ws$. When $z=|u|$, position $z$ is the separator after $u$, but position $z+1$ is the first position of the nonempty field $v$. The field-content identity at the start of $v$, together with the shift property (`Turing.fieldsTape_cons_shift`), shows that this latter cell contains a symbol. Finally, if $z>|u|$, shift both queried positions past $u$ and its separator. The shifted first position is nonnegative, and the endpoint bound becomes the corresponding strict endpoint bound for $v::ws`, using the offset-after-a-leading-field identity (`Turing.fieldOffset_cons_succ`). The induction hypothesis rules out blankness at both shifted positions, and the shift property transfers that conclusion back to the original tape.

**Key facts.** `Turing.fieldsTape_field`, `Turing.fieldOffset_cons_succ`, `Turing.fieldsTape_cons_shift`.
