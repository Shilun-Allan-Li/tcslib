<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_template_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Explicit Record Template

**Claim.** For any types $Q,T$ and natural numbers $n,s$, the record template is the two-field list whose first field is the binary expansion of $n+1$ encoded as digit symbols and whose second field is the $2s+1$-symbol centered cell pattern, with blank contents and marker true only at the middle position.

**Proof.** Expand the record template. Its first field is defined using the bit-test list of width equal to the length of the binary expansion of $n+1$. The identity `Turing.binDigits_posWidth_succ` identifies that list with the bits of $n+1$. For the second field, `Turing.rt_centeredWord` identifies the marker pattern obtained by ranging over the $2s+1$ positions and marking exactly the central index with the word consisting of $s$ false bits, one true bit, and $s$ false bits. Mapping both lists into their respective digit and cell symbols gives the claimed two-field form.

**Key facts.** `Turing.binDigits_posWidth_succ`, `Turing.rt_centeredWord`.
