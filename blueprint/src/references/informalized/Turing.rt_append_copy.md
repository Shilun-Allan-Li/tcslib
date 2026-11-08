<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_append_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Record to the Table

**Claim.** The constructed machine appends the record encoding after the table fields within a linear time and head-displacement bound, reaches its exit state for the first time then, and leaves all other configuration data and tape contents unchanged.

**Proof.** Let $D$ be the offset of the end of all table fields. The field-offset length identity (`Turing.fieldOffset_length`) gives $D=|\mathrm{joinFields}(\mathrm{tableFields}(h,es))|+1$, and the table-offset identity (`Turing.tableOffset_length`) identifies this with the requested append position. The machine first uses the end-seeking routine (`Turing.seekEndTM_run_ofCfg`) to move tape 0's head from $o$ to $o+D$. Its hypotheses follow from the assumed table contents and nonempty fields. It then changes to the entry state of the record-copy machine supplied by `Turing.rt_fieldsCopy_reverse`. Tape 1 still has the record at its head, and tape 0 is blank from the new head onward, so that machine's hypotheses hold. It copies the record and provides a time bound, a first-arrival exit property, and head-displacement bounds relative to its starting positions. The seam-composition result (`Turing.rt_copy_seam`) joins the scan and copy phases: the first exit cannot occur during the scan or before the copy phase finishes, and their displacement bounds combine. The chosen constant $C+4$ absorbs the scan length and the copy-machine bound into the claimed linear budget. At the endpoint, the copied interval begins at $o+D$; the copy routine's tape description and the original blank-tail assumption show that tape 0 has exactly the specified appended encoding, with other cells and configuration fields unchanged.

**Key facts.** `Turing.fieldOffset_length`, `Turing.tableOffset_length`, `Turing.seekEndTM_run_ofCfg`, `Turing.rt_fieldsCopy_reverse`, `Turing.rt_copy_seam`.
