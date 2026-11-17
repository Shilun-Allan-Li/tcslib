<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_reset_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reset Scan to the Left Boundary

**Claim.** For $j\le |x|$, starting in reset-scan phase with input head at position $j$, after $j$ steps the input head is at position $0$, while the rest of the configuration is unchanged.

**Proof.** Proceed by induction on $j$. At zero steps the claim is immediate. For the successor case, the head is at position $j+1$, within the word by the length bound, so it reads the corresponding symbol of $x$. In reset-scan, any input symbol triggers a leftward input-head move and leaves all controller tapes and heads unchanged. The setup-configuration action formula (`Complexity.setupCfg_apply`) records this effect, and the move sends position $j+1$ to $j$. The induction hypothesis then applies to the remaining $j$ steps, completing the scan to position zero without changing the other configuration data.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.setupCfg_input`, `Complexity.setupCfg_apply`.
