<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_field_cover -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coverage by a Joined Field

**Claim.** For a nonempty list of fields, every offset from $-1$ through the length of their joined list lies within the inclusive offset range of at least one field.

**Proof.** Because the list of fields is nonempty, its last index is valid. The field-offset recurrence (`fieldOffset_succ`) and the endpoint identity (`fieldOffset_length`) show that the endpoint immediately after the last field is one more than the joined-list length. Thus at least one field ends at or beyond the given position. Choose the first index $j$ whose field endpoint is at or beyond $p$; such an index exists by the endpoint calculation. This gives the upper bound on $p$ relative to field $j$. If $j=0$, its offset is zero, so the assumed lower bound $p\ge -1$ gives the required lower bound. If $j>0$, minimality says the preceding field endpoint is strictly before $p$. The recurrence says the next field begins one position after that endpoint, so $p$ is at least one less than the next field's starting offset. This is exactly the lower bound $p-\operatorname{fieldOffset}(fs,j)\ge -1$.

**Key facts.** `Turing.fieldOffset_succ`, `Turing.fieldOffset_length`.
