<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.fieldsTape_field -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape contents within a field

**Claim.** For a field indexed by $j$ and $-1\le p\le |fs_j|$, the joined-fields tape at its offset plus $p$ equals the buffer tape of that field at $p$.

**Proof.** Proceed by induction on the field index. For the first field, its offset is zero. If $p<0$, the lower bound forces $p=-1$, so both tape definitions give blank. If $p\ge0$, the queried position lies either within the first field, where joining stores its symbols, or at its endpoint. In the latter case, when another field follows, the position is the separator and is blank; when no field follows, the joined list ends there and is also blank. These are exactly the buffer-tape values for positions in the stated range.

For a later field, write the list as $u::v::fs$. Its offset is $|u|+1$ plus the offset of the corresponding field in $v::fs$ (`Turing.fieldOffset_cons_succ`). Apply the shift property for joined fields (`Turing.fieldsTape_cons_shift`) to move past $u$ and its separator. The position remaining is at least $-1$, so that shift applies. The induction hypothesis for $v::fs$ then identifies the tape value with the buffer tape of the selected field.

**Key facts.** `Turing.fieldOffset_cons_succ`, `Turing.fieldsTape_cons_shift`.
