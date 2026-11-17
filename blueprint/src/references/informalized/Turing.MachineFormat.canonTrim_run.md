<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonTrim_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the tape trimming machine

**Claim.** Starting in the forward-pass state with words on the work tapes, the trimming machine finishes after exactly $2|w(i)|+2$ steps, with tape $i$ replaced by its trailing-one-stripped word and every other tape unchanged; it does not reach the completed state earlier.

**Proof.** Write $w=words(i)$, let $m$ be the length of its trailing-one-stripped prefix, and use the boundary properties of that prefix: it is the initial segment of $w$ of length $m$, every position at or beyond $m$ is $1$, and when $m>0$ the bit just before position $m$ is $0$. During the forward pass, the head moves right across the $|w|$ bits without changing them, then at the first blank cell turns into the backward state. During the backward pass, it moves left. Once it has passed the prefix boundary (the clean flag is set), every bit encountered is a trailing $1$ and is erased; the tape erasure fact (`canonEraseLast`) identifies this update with deleting the last symbol of the represented word. Before the boundary, the machine leaves symbols in place: the boundary bit is $0$, so the clean flag cannot trigger an erasure there. Thus after the backward pass reaches the left blank cell, the tape contains exactly the stripped prefix. The initial rightward traversal takes $|w|$ steps, the return traversal takes $|w|$ steps, and the turn and entry into the completed state add two steps, for a total of $2|w|+2$. The configuration trace theorem (`catalog_trace_run`) packages these forward, turn, backward, and entry transitions into the full run; its phases show that the completed state occurs only at the final entry time.

**Key facts.** `Turing.MachineFormat.canonStrip_boundary`, `Turing.MachineFormat.canonEraseLast`, `Turing.catalog_trace_run`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`, `Turing.step_of_tapeAction_move`, `Turing.step_of_tapeAction_write`.
