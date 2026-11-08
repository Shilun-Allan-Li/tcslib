<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.TableAt.recordAt_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extracting a record from a table entry

**Claim.** Under the stated table layout and well-formedness assumptions, if the head is at the start of entry $e_j$ with the specified offset, then for every positive $m_0\le m$ the tape beginning at the head represents the first $m_0$ fields of that entry as a record.

**Proof.** Split the table fields into a prefix consisting of the header and the entries before $e_j$, the selected block $g_s=e_j.take\ m_0$, and a suffix consisting of the rest of $e_j$ followed by later entries. The list identities for taking and dropping at index $j$ give this decomposition of the full table. Since $e_j$ has length $m$ and $0<m_0\le m$, the selected block is nonempty. The field-layout slicing theorem (`rt_fields_slice`) says that, in a concatenation of a prefix, this nonempty block, and a suffix, the tape contents at positions measured from the start of the block agree with the record layout for the block, throughout its record range. The offset of the prefix is exactly `tableOffset h es j`. Using the assumed head position, a position $p$ relative to the head is therefore the corresponding position `tableOffset h es j + p` in the table. The slicing bound ensures this position is within the range covered by `TableAt`; applying that table representation and then the slice identity gives the required tape contents for every $p$ in the range defining `RecordAt`.

**Key facts.** `Turing.rt_fields_slice`.
