<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_borrow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full-Width Budget Borrow Pass

**Claim.** After $|w|$ steps of the borrow phase, the budget head has advanced to $1+|w|$, the budget tape contains the rewritten word from the fixed-width borrow pass, and the carry is its final carry; all other specified configuration data are preserved.

**Proof.** The run lemma for the budget lane (`Complexity.obliviousSchedule_borrow_run`) follows the borrow computation across the bits of $w$: it updates each bit by exclusive-or with the incoming carry, propagates the carry, and advances the head once per bit. To express that lane computation as a setup configuration, use the lane-to-setup correspondence (`Complexity.laneCfg_setup`). The clock tape is represented by the sweep of the origin marker followed by the encoded bits (`Complexity.clockTape_zipper`), and after the pass the reversed rewritten bits followed by the origin marker form the same clock tape, by `Complexity.clockTape_zipper_end`. Finally, the borrow operation preserves word length (`Complexity.budgetBorrow_length`), so the final head position is $1+|w|$. The remaining setup components are unchanged under the lane correspondence.

**Key facts.** `Complexity.obliviousSchedule_borrow_run`, `Complexity.laneCfg_setup`, `Complexity.clockTape_zipper`, `Complexity.budgetBorrow_length`, `Complexity.clockTape_zipper_end`.
