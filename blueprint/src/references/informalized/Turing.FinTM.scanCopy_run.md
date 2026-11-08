<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.scanCopy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Prefix by Scanning

**Claim.** After $j$ steps from the scan configuration at position $0$ in state $q$ with output $o$, the machine is in state $q$ at position $j$ with output $o$ followed by the first $j$ entries of $x$, for every $j\le |x|$.

**Proof.** Proceed by induction on $j$. At $j=0$, the run has taken no steps, and the scan configuration has output $o=o++x.take\ 0$. For the successor case, use the induction hypothesis to identify the configuration after $j$ steps. Since $j<|x|$, its scanned symbol is the $j$th bit of $x$ (`scanCfg_read`, together with the list lookup identity). The assumed transition emits that bit, moves right, and returns to $q$. A right move from this interior position advances the scan position from $j$ to $j+1 (`moveInputPos_pos_of_ne_right`). The output is therefore extended by the next bit, which is exactly $o++x.take (j+1)$. The state, position, and output determine the configuration when there are no work tapes (`Cfg.ext_zero_tapes`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.scanCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
