<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission of a Stack Word

**Claim.** For any program, input-head position, Boolean word on the main stack, output word, and optional pending bit, the bridging machine can reach a halted configuration with the main stack reduced to the terminator, the other stacks unchanged, and output extended by the pending bit, if present, followed by the bits of the word.

**Proof.** Induct on the Boolean word. If it is empty, the main stack word is the sentinel bit followed by the terminator. The emitting state reads and removes the sentinel bit, appending the pending bit to the output if one exists, and records the sentinel bit as the new pending bit. The next step sees the terminator rather than a bit and enters the halted state without changing the stacks or output. The head reading fact (`bridgeCfg_read`) identifies the symbol seen by the machine, and the idle transition fact (`bridgeCfg_idle`) identifies the final step; the run recurrence (`runFrom_succ_eq_step'`) expresses these as a two-step run. For a nonempty word beginning with $b$, the emission transition removes its first bit symbol, leaves the remaining stack word, appends the old pending bit if present, and makes $b$ the pending bit (`bridge_emit_step`). This gives a one-step reach to the configuration for the shorter word. Apply the induction hypothesis to that remaining word with pending bit $b$, then concatenate the one-step and inductive runs using transitivity of reachability (`bridgeReach_trans`). The output concatenation is the old pending bit followed by the bits of the original word, as required.

**Key facts.** `Turing.bridgeCfg_idle`, `Turing.bridgeCfg_read`, `Turing.bridgeReach_trans`, `Turing.bridge_emit_step`.
