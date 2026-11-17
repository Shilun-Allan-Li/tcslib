<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferedFirstCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-step first-phase simulation

**Claim.** When the first machine's configuration is not halted, one step of the buffered composition from its first-phase embedding equals the first-phase embedding of the first machine's one-step successor.

**Proof.** Since $c$ is not halted, write its state as $q$ and consider the transition action $a$ chosen by $M_1$ from $q$, the current input symbol, and the symbols under its work-tape heads. In the first-phase embedding, the physical input position and the left work-tape block agree with those of $c$, so the buffered machine reads exactly the same input and work-tape symbols and chooses this same action. Its transition stores the action's output, if any, in the buffer cell at the current buffer head and advances that head; all other work-tape actions in the left block match $a$, while the right block remains blank. The identity that appending one output bit extends the buffer tape by writing that bit at the previous end (`bufferTape_append`) shows that the updated buffer and head position are precisely those prescribed by the first-phase embedding of $a$ applied to $c$. The state, input-head position, and external output also agree, proving equality of the configurations.

**Key facts.** `Turing.FinTM.bufferTape_append`.
