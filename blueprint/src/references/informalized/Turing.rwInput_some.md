<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.rwInput_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind Across an Input Symbol

**Claim.** When the input head is at a position $p$ with $1\le p\le |x|$, one step in state $\mathrm{rwInput}$ moves it to $p-1$, while preserving the tapes, work-head positions, state, and output.

**Proof.** The input head at position $p$ scans the symbol $x[p-1]$: this is the input-symbol identification fact (`Turing.inputSymbolInner`), applied with index $p-1$, which lies within the word by the assumed bounds. In state $\mathrm{rwInput}$, the transition on any scanned symbol is the control action that moves left, returns to $\mathrm{rwInput}$, and leaves all work tapes and output untouched. The left-move formula (`Turing.moveInputPos_neg_of_ne_left`) applies because $p\ge1$, and gives input position $p-1$. The action’s zero work-tape movements preserve every work-head position, and it writes and outputs nothing, so the full configuration has the asserted form.

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_neg_of_ne_left`.
