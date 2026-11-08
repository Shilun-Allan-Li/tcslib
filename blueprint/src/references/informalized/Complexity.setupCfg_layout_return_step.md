<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_layout_return_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Return-Sweep Step

**Claim.** When the unary tape does not read the origin marker in layout-return phase $i$, one step advances the phase to $i+1\pmod 3$, moves the unary head left exactly when $i=2$, and moves the guide head left once, without changing tape contents or other configuration data.

**Proof.** The setup configuration reads the unary tape at its unary head position, so its scanned symbol is $\mathrm{ut}(u)$. Since this is not the origin marker, the transition takes the non-origin branch of layout-return. That branch advances the phase using `nextThird`, leaves the budget tape fixed, makes no writes, moves the unary head left when $i=2$ and otherwise holds it, and moves the guide head left. The setup-configuration action formula (`Complexity.setupCfg_apply`) translates these actions into the displayed head positions and unchanged tape contents; the input head also stays put.

**Key facts.** `Complexity.setupCfg_apply`.
