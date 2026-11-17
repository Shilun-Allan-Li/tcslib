<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweepRevCfg_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationary Write in a Backward Zipper

**Claim.** Applying the action that writes $b$, leaves the work head stationary, and enters state $q'$ yields the backward-sweep configuration with state $q'$, input-head position $p$, frontier $z$, left stack $l$, right stack $b::r.tail$, and unchanged output.

**Proof.** The state becomes $q'$, the input-head position is fixed by zero input movement (`Turing.moveInputPos_zero`), and the output is unchanged because the action emits nothing. The work head remains at $z$, since its movement is zero. For each tape coordinate, the action updates the represented tape at $z$ with value $b$. The zipper write identity says that this update is represented by the same frontier and left stack, with right stack $b::r.tail$ (`Turing.FinTM.sweepTape_write`). The head position and all remaining fields therefore match the stated configuration.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.FinTM.sweepTape_write`.
