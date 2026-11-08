<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitPrepare_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation Scan

**Claim.** For every natural number $k$, Boolean words $w,s$, and natural number $j\le |s|$, running the split-preparation machine for $j$ steps from the scan configuration at position $0$ yields the scan configuration at position $j$.

**Proof.** Induct on $j$. The zero-step case is immediate. For the successor case, the induction hypothesis identifies the run after $j$ steps with the scan configuration at position $j$. Since $j<|s|$, the first work-tape head reads the $j$th symbol of $s$. The machine therefore advances to scan position $j+1$ and moves the heads across the other tapes one cell to the right. The input head advances from $\min(j,|w|)+1$ to $\min(j+1,|w|)+1$ (`f2_splitPos_succ`); its comparison flag updates to record whether $|w|<j+1$ (`f2_splitCount_over`). On every other tape, writing true at cell $j$ extends the catalog from cells $j+1$ through $|s|$ to cells $j$ through $|s|$ (`f2_catalogPolyTape_write`). The first tape and output remain unchanged, and the heads advance as specified. The successor run identity (`runFrom_succ_eq_step'`) completes the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_splitPos_succ`, `Turing.FinTM.f2_splitCount_over`, `Turing.FinTM.f2_catalogPolyTape_write`.
