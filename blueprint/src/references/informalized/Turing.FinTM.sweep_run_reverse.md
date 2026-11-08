<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweep_run_reverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Sweep by a Local Rule

**Claim.** If each transition on an encoded cell implements the local rule and moves left, then scanning the encoded word from right to left applies the rule successively, writes the transformed word, decreases the frontier by the word length, and preserves the input position and output.

**Proof.** Induct on the scanned word, allowing the controller, frontier, and left stack to vary. For the empty word, zero steps leave the configuration unchanged. For a nonempty word $a::as$, the backward-facing tape also reads its first right-stack entry at the frontier; `sweepTape_read`, applied at the reflected coordinate, identifies that symbol. By the transition hypothesis, the machine performs the local update and moves left. The backward zipper identity (`sweepRevCfg_left`) puts the transformed cell at the front of the left stack, decreases the frontier by one, and removes the consumed symbol from the right stack. The induction hypothesis handles the remaining word. Unfolding the fold and reversing the accumulated transformed word gives the claimed stack arrangement; the frontier changes by minus the total word length. Input position and output are preserved throughout.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.sweepTape_read`, `Turing.FinTM.sweepRevCfg_left`, `Turing.MultiTapeTM.runFrom_zero`.
