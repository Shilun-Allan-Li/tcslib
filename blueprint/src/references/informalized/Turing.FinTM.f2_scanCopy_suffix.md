<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_scanCopy_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Suffix

**Claim.** If the input word is the concatenation of a prefix and a suffix, then scanning from the end of that prefix copies the suffix to the output and halts at the end of the input after one step per suffix symbol plus one.

**Proof.** Induct on the suffix. For the empty suffix, the machine is positioned at the blank immediately after the input. Its specified blank transition emits nothing and halts; the resulting configuration has the original output and head position at the input end. For a suffix beginning with a bit $b$, the head is on $b$. The transition copies $b$, moves right, and leaves the state at $q$, so the configuration becomes the scan configuration at the next position with output extended by $b$. Apply the induction hypothesis to the remaining suffix, starting with the extended prefix and output. The resulting output is the original output followed by the entire suffix, and the number of steps is its length plus one. The scan-configuration reading fact identifies the symbol under the head, and the right-move fact gives the next head position; configuration extensionality for zero work tapes reduces equality to state, position, and output.

**Key facts.** `Turing.FinTM.f2_scanCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
