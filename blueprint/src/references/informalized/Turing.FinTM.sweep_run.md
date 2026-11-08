<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweep_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Sweep by a Local Rule

**Claim.** If each transition on an encoded cell implements the local rule, then scanning a finite encoded word from left to right applies that rule successively, writes the resulting encoded word, advances the frontier by the word length, and preserves the input position and output.

**Proof.** Induct on the scanned word, allowing the controller state, frontier, and left stack to vary. For the empty word, the run has length zero and the fold leaves the controller and word unchanged. For a nonempty word $a::as$, the tape head is at the frontier and reads the encoded first cell; this is the content of `sweepTape_read`. The transition hypothesis identifies the machine action there with the local rule applied to the current controller and $a$. The zipper update for a rightward move (`sweepCfg_right`) writes the transformed cell onto the left stack, advances the frontier by one, and removes the consumed cell from the right stack. Apply the induction hypothesis to the remaining word. Unfolding the fold shows that its controller is the successive local-rule result and its output word is the transformed cells in their original order; reversing that word onto the left stack gives the asserted configuration. The frontier arithmetic adds one to the remaining scan length, while input position and output are unchanged at every step.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.sweepTape_read`, `Turing.FinTM.sweepCfg_right`, `Turing.MultiTapeTM.runFrom_zero`.
