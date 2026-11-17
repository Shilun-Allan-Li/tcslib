<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact decorated simulator step

**Claim.** The simulator's one-step successor from the decorated configuration is the decorated successor of the schedule controller, with the transducer's updated finite data, prescribed writes at the current head coordinate, and output appended.

**Proof.** Apply the general one-step theorem for a decorated machine (`decoratedCfg_step`) to the schedule controller, using its current phase and the data state and tapes. That theorem says that the controller performs its own transition while the visit function determines the new data state, writes on the added tapes at the controller's selected head position, and any output appended to the output word. Here the selected head is the guide-tape head, which is at $g$ in the macrostep configuration. Substituting the definitions of the macrostep and decorated configurations identifies that head position with $g$ and yields exactly the asserted successor, including the transducer's reads from the data tapes at $g$.

**Key facts.** `Complexity.decoratedCfg_step`.
