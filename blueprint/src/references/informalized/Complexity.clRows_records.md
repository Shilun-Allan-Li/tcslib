<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRows_records -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recorder Equals Generic Row Stream

**Claim.** For every finite Boolean Turing machine, Boolean input word, and natural number $n$, the generic stream of the first $n$ packed rows of movement-count bit representations equals the recorder’s serialized trajectory prefix of $n$ rows.

**Proof.** Induct on $n$. At zero, both streams are empty. For the successor step, expand each stream by its recursive definition and use the induction hypothesis for the preceding rows. The identity `clRowPrefix_fields` identifies the stored prefix of the current row with the packed encoding of the list of its fields. Since this list has length at most the number of fields, taking that many entries leaves it unchanged. Thus the newly appended row agrees with the recorder’s row, proving equality of the extended streams.

**Key facts.** `Complexity.clRowPrefix_fields`.
