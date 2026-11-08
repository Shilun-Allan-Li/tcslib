<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitPrepare_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation scan configurations

**Claim.** For each $j\le |s|$, running the preparation machine for $j$ steps from the initial scan configuration yields the asserted scan configuration at count $j$.

**Proof.** Induct on $j$. At zero, the initial scan configuration is the claimed one. For the successor step, the bound ensures $j<|s|$, so the first work head scans the $j$-th bit of $s$. The scan transition advances the input and work heads, writes a $1$ at the current end of the unary scratch tape, and updates the flag to record whether the input has passed the end of $w$. The flag update is justified by `splitCount_over`; the head position update is `splitPos_succ`; and the scratch-tape extension is `catalogPolyTape_write`. The first tape and output remain unchanged, while the work-head positions advance to $j+1$. Applying the run-after-successor identity (`runFrom_succ_eq_step'`) completes the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.splitCount_over`, `Turing.FinTM.splitPos_succ`, `Turing.FinTM.catalogPolyTape_write`.
