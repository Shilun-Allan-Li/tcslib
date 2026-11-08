<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_lane_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Lane Finite-State Transduction

**Claim.** Under the stated transition rule, running the machine for the length of the word performs the left-to-right register transduction on the selected lane, advances the frontier by that length, and places the reversed rewritten word on the left of the zipper.

**Proof.** Induct on the scanned word, allowing the register, frontier, and left list to vary. For the empty word, zero steps leave the configuration unchanged, and the fold over an empty word has the initial register and no rewritten symbols.

For a word with first symbol $a$ and tail $as$, the active-lane read lemma (`Turing.timed_laneCfg_read`) shows that the head of the right list is the encoding of $a$. The assumed transition rule therefore makes the first machine step write the encoding of the updated cell, move the selected head right, and update the register. The right-moving zipper identity (`Turing.timed_laneCfg_right`) describes this new configuration: its frontier is $z+1$, its left list begins with the rewritten symbol, and its right list is the tail followed by the untouched remainder.

Apply the induction hypothesis to that tail, starting from the updated register, frontier, and left list. The defining recursion for the sweep fold says that this is precisely the transduction of the original word. Its rewritten symbols are accumulated in scan order and then reversed onto the left list, while the frontier advances by one plus the tail length. The successor-run identity (`Turing.MultiTapeTM.runFrom_succ_eq_step`) identifies the first step followed by the tail run with the full run; the zero-run identity (`Turing.MultiTapeTM.runFrom_zero`) handles the base case.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.timed_laneCfg_read`, `Turing.timed_laneCfg_right`.
