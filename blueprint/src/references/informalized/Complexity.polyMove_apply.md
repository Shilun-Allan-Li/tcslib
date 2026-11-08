<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.polyMove_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Single-Head Move

**Claim.** Applying the specified action preserves the input-head position, work tapes, and output, changes the state to $s'$, and changes only work-head position $i$, by adding $d$.

**Proof.** Compare the two configurations field by field. The action sets the state to $s'$. Its input-head movement is zero, so the input position is unchanged by the zero-move property (`Turing.moveInputPos_zero`). No work-tape symbols are written, so the tape contents are unchanged. For the head positions, the action assigns movement $d$ at index $i$ and zero elsewhere; thus the resulting position function is exactly the update of $h$ at $i$ with value $h(i)+d$. Finally, the action emits no symbol, so appending its output leaves the existing output word $o$ unchanged. These equalities establish equality of the configurations.

**Key facts.** `Turing.moveInputPos_zero`.
