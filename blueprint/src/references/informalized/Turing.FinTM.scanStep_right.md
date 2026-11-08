<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.scanStep_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Right-Moving Scan Step

**Claim.** Under the stated transition assumption, one step from the scan configuration at position $i$ in state $q$ produces the scan configuration at position $i+1$ in state $q'$, with output extended by the optional emitted symbol.

**Proof.** The scan configuration at position $i$ reads the symbol $x[i]?$, by the scan reading identity (`scanCfg_read`). Thus the assumed transition is precisely the action taken: it moves right, leaves the work tapes unchanged, emits `emit`, and enters $q'$. Because $i<|x|$, this is not the right-end position, so a right move advances the encoded input position from $i+1$ to $i+2$, corresponding to scan position $i+1$ (`moveInputPos_pos_of_ne_right`). The action appends `emit.toList` to the output. These state, position, and output equalities establish equality of the configurations (`Cfg.ext_zero_tapes`).

**Key facts.** `Turing.FinTM.scanCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
