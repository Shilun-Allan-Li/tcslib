<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean :: Turing.vhostEmitTM_emitting_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emitting Transition That Halts

**Claim.** If the original machine's transition from $c$ halts and emits bit $a$, then one virtual simulation step from the constructed configuration has no state and output $\mathrm{pre} ++ c.output ++ [a]$.

**Proof.** The one-step simulation theorem (`vhostEmitTM_step`) identifies the virtual step with the virtual configuration built from the original machine's one-step successor, for a suitable updated boundary tag. Since $c$ has state $q$, the original step uses the transition specified in the hypotheses. Its successor state is none and its emitted output is $a$. By the definition of the virtual configuration, its output is the prefix followed by the original output and then the output of that step. Associativity of list concatenation gives the stated list.

**Key facts.** `Turing.vhostEmitTM_step`.
