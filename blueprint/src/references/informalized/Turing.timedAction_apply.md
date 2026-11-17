<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Applying a Lifted Action

**Claim.** Applying the six-tape lift of an interpreter action to the six-tape lift of a configuration with clock word $clock$ gives the lift of the configuration after the original action, with the same clock word.

**Proof.** Configurations are equal once their state, input-head position, tape contents, work-head positions, and output agree. The state, input position, and output agree directly from the definitions. For tape contents, check each of the six lanes. On the four interpreter lanes, the lifted action performs exactly the original write instruction at the original head position. On the clock lane it makes no change. On the buffer lane, the interpreter action's output is either absent, leaving the buffer unchanged, or is a bit $b$, in which case the buffer word grows from $clock$ to $clock++[b]$. The buffer-tape append identity (`Turing.FinTM.bufferTape_append`) says this is exactly the update of the buffer tape at position $|clock|$. The head positions also agree lane by lane: the four original positions follow the original action, the clock position remains $|clock|$, and the buffer position advances by one precisely when an output bit is emitted. Thus every component of the lifted configurations agrees.

**Key facts.** `Turing.FinTM.bufferTape_append`.
