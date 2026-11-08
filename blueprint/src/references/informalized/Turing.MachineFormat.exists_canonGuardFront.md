<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonGuardFront -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Guard Check with Framing

**Claim.** For every machine format $F$, a finite Boolean-alphabet machine with at least four work tapes can check the canonical guard condition on a parsed input within linear time, reach the prescribed yes or no state and input-head position, produce no output, and leave the specified tapes in their ready contents.

**Proof.** Begin with a machine that prepares the canonical ready words from the parsed header, and a separate machine that seeks the input head to the position encoded by the canonical offset word. The offset specification identifies that position as $2|bits|+3$ and bounds the offset word's length. Embed the seeker into the preparation machine's tape bank; the embedding preserves the other tapes and its run agrees with the original run on the selected tapes (the run and framing properties of `embedEmitTM_runFrom` and `embedEmitTM_frame`). At the reached position, start the binary guard checker on tape 1. The guard-run lemma supplies a time-linear check: it reaches `done` exactly when $B(v+1)\le |rest|$, and otherwise escapes to the right end; it produces no output. Here $B=\max\{guard,(4k+5)3^{k+1}\}$. By framing, all tapes outside the checker bank retain their ready contents. In the successful case, the guard leaves the input head beyond the target position, so run the seeking machine again to return it there; in the unsuccessful case, it is already at the right end. Compose these stages at their designated seam states. Their time bounds add, and the input-length and offset bounds show that the total is at most a constant times $|\alpha|+1$. The seam-composition result gives the final configuration, while its cut condition ensures the stages hand off at the intended first exit times.

**Key facts.** `Turing.MachineFormat.exists_canonReadySeam`, `Turing.MachineFormat.exists_canonSeekOnBank`, `Turing.MachineFormat.canonOffset_spec`, `Turing.MachineFormat.canonGuard_run`, `Turing.embedEmitTM_runFrom`, `Turing.embedEmitTM_frame`, `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_runFrom_left`.
