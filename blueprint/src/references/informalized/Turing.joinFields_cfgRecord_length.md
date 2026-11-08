<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.joinFields_cfgRecord_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Joined Configuration Record

**Claim.** The joined fields of the record formed from $s$, a configuration $c$, and a tag $\tau$ have length $k(2s+1)+w(|x|)+k+4$.

**Proof.** The record has $k+3$ fields: one state field of length $1$, one input-position field of length $w(|x|)$, one work-cell field of length $2s+1$ for each of the $k$ tapes, and one tag field of length $1$. By the joined-fields length formula (`joinFields_length`), joining a nonempty list of fields gives the sum of their lengths plus the number of fields minus one. The sum of the field lengths is $1+w(|x|)+k(2s+1)+1$. Adding $(k+3)-1$ separators yields $k(2s+1)+w(|x|)+k+4$, as claimed; the record’s field count is supplied by `cfgRecord_length`.

**Key facts.** `Turing.joinFields_length`, `Turing.cfgRecord_length`.
