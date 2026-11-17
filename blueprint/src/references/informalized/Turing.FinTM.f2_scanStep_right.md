<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_scanStep_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Rightward Scan Step

**Claim.** When the transition on the bit currently under the head moves right, emits the specified optional bit, and enters the specified optional state, one scan step advances the scan position by one and appends that emitted bit, if any, to the output.

**Proof.** The scan configuration at position $i$ reads the $i$th input bit, by the scan-configuration reading fact (Turing.FinTM.f2_scanCfg_read). The transition hypothesis therefore determines the action: it moves right, changes to state $q'$, and emits `emit`. Applying this action leaves the output as $o$ followed by the list represented by `emit`. Since $i<|x|$, the head is not at the right boundary, so a right move places it at position $i+1$ (Turing.moveInputPos_pos_of_ne_right). There are no work tapes, and configuration extensionality for zero work tapes (Turing.Cfg.ext_zero_tapes) now gives the claimed equality.

**Key facts.** `Turing.FinTM.f2_scanCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
