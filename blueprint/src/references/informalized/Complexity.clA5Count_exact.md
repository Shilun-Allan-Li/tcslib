<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Count_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact stored movement counts

**Claim.** For every cursor, every time within the producer horizon, and every movement-count coordinate, the count stored in the packed word equals the corresponding count along the machine’s trajectory on the all-false input of the specified length.

**Proof.** The packed-data exactness lemma (\texttt{clA5Data_exact}) identifies the packed word’s stored trajectory with the serialization of the machine’s count rows, and identifies its stored horizon with the producer horizon. By the count-row serialization identity (\texttt{clRows_records}), those serialized rows are exactly the record list used in the packed data. The row-field decoding lemma (\texttt{clA5Field_rows}) then extracts, at index $t$ and coordinate $i$, the binary encoding of the desired count; the hypothesis that $t$ is within the horizon ensures this row is present. Converting that bit encoding back to its number using (\texttt{clNum_bits}) shows that the extracted number is the trajectory count. The stored value is capped by the horizon, but the count-bound lemma (\texttt{clCounts_bound}) and the time hypothesis show the count is already at most that horizon, so the cap leaves it unchanged.

**Key facts.** `Complexity.clA5Data_exact`, `Complexity.clRows_records`, `Complexity.clA5Field_rows`, `Complexity.clNum_bits`, `Complexity.clCounts_bound`.
