<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputLength.lean :: Turing.inputLength_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing a Buffered Tape Symbol

**Claim.** If the transition in the specified buffered configuration writes the $r$th symbol of $w$, leaves the input head fixed, moves the work head by $m$, and enters phase $s'$, then one step produces the configuration buffering the first $r+1$ symbols, with the stated phase, input position, and work-head displacement.

**Proof.** The transition hypothesis identifies the machine's action as writing $w[r]$ on the work tape, keeping the input head still, moving the work head by $m$, and entering $s'$. The one-step action rule for such a write (`Turing.step_of_tapeAction_write`) gives exactly those component changes. The work-tape contents are updated at the cell at offset $r$; since $r<|w|$, the catalog write lemma (`Turing.catalog_write_take`) identifies this updated tape with the buffer extended from its first $r$ symbols to its first $r+1$. The zero input movement leaves the input position unchanged (`Turing.moveInputPos_zero`), and the head position becomes the original position plus $r+m$. The remaining configuration components agree directly.

**Key facts.** `Turing.step_of_tapeAction_write`, `Turing.catalog_write_take`, `Turing.moveInputPos_zero`.
