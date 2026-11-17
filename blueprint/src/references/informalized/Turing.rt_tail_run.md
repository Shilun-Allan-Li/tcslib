<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_tail_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Tail-Field Construction

**Claim.** The tail machine writes the concatenation of $k$ copies of $w$, with blank separators, followed by the final symbol, and reaches its prescribed exit state for the first time within $(k+1)(4|w|+12)$ steps. Every head remains within distance $|F|+1$ of its initial position, and the final configuration differs only by the exit state and the destination field $F$.

**Proof.** Proceed by induction on the number $k$ of copies. When $k=0$, the machine writes the one-symbol word containing the final symbol and returns to its exit state. The constant-word run theorem (`Turing.writeConstTM_run_ofCfg`) supplies the exact final tape contents, first-exit property, and head bound; the field representation reduces to this one-symbol field.

For the successor case, write the field list as its first word $w$ followed by the remaining fields. First use `Turing.copyTM_run_ofCfg` to copy $w$ from the source tape to the destination. The initial blank-slot hypothesis ensures this copy overwrites only the intended destination segment. Then `Turing.skipTM_run_ofCfg` moves past the copied word and its separator, placing the destination head at the start of the remaining field. The induction hypothesis applies there: the source word is still available, and the translated blank-slot condition follows from the original one. It constructs the tail fields with their stated exit and head bounds.

Next `Turing.skipBackTM_run_ofCfg` returns across the first copied field to the original destination position. The concatenation formula for joining fields (`Turing.joinFields_cons_cons`) identifies the layout as the first word, a blank separator, and the recursively constructed remainder. The field identities `Turing.fieldsTape_field` and `Turing.fieldsTape_cons_shift` verify the tape contents on the first field and on the shifted tail, including the separator boundary. The successive runs are combined with `Turing.rt_copy_seam`, which preserves the first-exit property and combines their head-radius estimates. Their costs are bounded by the displayed recurrence, yielding $(k+1)(4|w|+12)$, while the radius is at most the total field length plus one.

**Key facts.** `Turing.writeConstTM_run_ofCfg`, `Turing.copyTM_run_ofCfg`, `Turing.skipTM_run_ofCfg`, `Turing.skipBackTM_run_ofCfg`, `Turing.joinFields_cons_cons`, `Turing.fieldsTape_field`, `Turing.fieldsTape_cons_shift`, `Turing.rt_copy_seam`.
