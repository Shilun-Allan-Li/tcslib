<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_layout_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Allocation Step

**Claim.** In an allocation phase, if the unary tape reads a unit marker and the guide tape reads the origin marker exactly at cell zero, one step advances the phase index modulo $3$, moves the unary head right exactly when the index is $2$, moves the guide head in the chosen direction, and writes the appropriate origin or interior marker at the guide cell previously scanned, leaving other configuration data unchanged.

**Proof.** First identify the scanned unary and guide symbols with $\mathrm{ut}(u)$ and $\mathrm{gt}(g)$ using the setup configuration. The unit-marker hypothesis selects the continuing allocation branch, and the guide hypothesis determines its write: the machine writes the origin marker when $g=0$ and the interior marker otherwise. It advances the phase with `nextThird`, moves the unary head right only in phase $2$, and moves the guide head according to the chosen direction. The setup-configuration action formula (`Complexity.setupCfg_apply`) gives the resulting configuration: it applies that write at the old guide-head position, updates the two head positions, and leaves the remaining data unchanged. The input-head movement is zero, hence its position is fixed by `Turing.moveInputPos_zero`. Splitting on the direction accounts for the right- and leftward allocation variants.

**Key facts.** `Complexity.setupCfg_apply`, `Turing.moveInputPos_zero`.
