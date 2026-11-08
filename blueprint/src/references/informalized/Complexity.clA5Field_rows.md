<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Field_rows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup in a Packed Row Stream

**Claim.** For any $t<N$ and coordinate $i<l$, field $tl+i$ in the packed stream of the first $N$ rows equals the $i$th field of row $t$.

**Proof.** Split the packed stream after row $t$. The split identity (`clRows_split`) writes it as the packed rows before $t$, followed by the packed fields of row $t$, followed by a remainder. Dropping the first $tl$ fields therefore leaves exactly row $t$'s packed fields followed by that remainder; this follows from the row-tail identity (`clA5Tail_rows`) together with the composition rule for tail operations (`clA5Tail_add`). Now select field $i$ from this remaining packed list. The packed-field recovery result (`clA5Field_fields`) identifies it with the $i$th entry of the field list for row $t$, which is the value at coordinate $i$. The index arithmetic is $tl+i$, as required.

**Key facts.** `Complexity.clRows_split`, `Complexity.clA5Tail_add`, `Complexity.clA5Tail_rows`, `Complexity.clA5Field_fields`.
