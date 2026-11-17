<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_adjacentWrites -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacent Tape Writes

**Claim.** Writing $u$ and then the immediately following word $v$ produces the same tape as writing their concatenation $u\mathbin{++}v$ at the original offset.

**Proof.** Fix a cell $q$. If $q$ lies in the interval occupied by $u$, both procedures return the symbol of $u$ at offset $q-o$. If it lies in the next interval, the concatenated word is read past the length of $u$, so its symbol there is exactly the symbol of $v$ at offset $q-(o+|u|)$. These identifications are the left and right indexing rules for list append. If $q$ lies in neither interval, it also lies outside the full concatenated interval, and both sides retain the original tape value. Thus the two tapes agree at every cell.
