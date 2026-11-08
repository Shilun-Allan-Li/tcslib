<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineWalk.lean :: Complexity.Meyer.wdec_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Bit Decision Step

**Claim.** If the output auxiliary tape contains false at its head, one step of the constructed machine leaves it in the waiting-decision state, writes true in that cell, and moves the auxiliary head one place right, with the other listed configuration data unchanged.

**Proof.** Unfold the constructed-machine step at the waiting-decision state. The third auxiliary-tape read is the value at the output tape’s head, hence is false by hypothesis ( `Complexity.Meyer.aux_read2`). The transition therefore writes true on that tape, moves its head right, leaves the other auxiliary tape and the simulated tapes and heads untouched, and remains in the waiting-decision state. The auxiliary-action calculation ( `Complexity.Meyer.lcfg_apply_aux`) expresses this as an update of the output tape at $z_O$ and a head position of $z_O+1$. The remaining coordinates agree by the definition of the encoded configuration.

**Key facts.** `Complexity.Meyer.lcfg_step`, `Complexity.Meyer.aux_read2`, `Complexity.Meyer.lcfg_apply_aux`.
