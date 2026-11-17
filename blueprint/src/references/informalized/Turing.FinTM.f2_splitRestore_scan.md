<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitRestore_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split Restoration Scan

**Claim.** For every natural number $k$, Boolean words $w,s$, and $j\le |s|$, running the split-restoration machine for $j$ steps from its scan configuration at position $0$ yields the scan configuration at position $j$. In that configuration the state is $(0,|w|<j)$, the input head is at $\min(j,|w|)+1$, the first work tape stores $s$, each other work tape contains true in cells $j\le z<|s|+1$ and is blank elsewhere, every work-tape head is at $j$, and the output is empty.

**Proof.** Proceed by induction on $j$. At $j=0$, the machine has run for zero steps, so the claimed equality is exactly the definition of the initial scan configuration.

For the induction step, suppose $j+1\le |s|$ and the scan description holds at position $j$. In particular, the first work-tape head reads the symbol $s[j]$, which exists because $j<|s|$. The machine is in its scanning state, and because that symbol is present, its transition moves the input head one position to the right, leaves the first work tape unchanged, erases cell $j$ on every other work tape, and moves all work-tape heads one position right. It emits no output. The fact that a run of $j+1$ steps is one step applied to the run of $j$ steps is the successor law for iteration (\texttt{Turing.MultiTapeTM.runFrom_succ_eq_step'}).

The input head therefore advances from $\min(j,|w|)+1$ to $\min(j+1,|w|)+1$ (\texttt{Turing.FinTM.f2_splitPos_succ}). The input symbol at the current position is present exactly when $j<|w|$, and otherwise is absent (\texttt{Turing.FinTM.f2_splitPos_read}). Thus the transition's state flag, which records whether the input symbol is absent, updates from $|w|<j$ to $|w|<j+1$. On each other work tape, erasing the cell at $j$ changes the set of true cells from $j\le z<|s|+1$ to $j+1\le z<|s|+1$ (\texttt{Turing.FinTM.f2_splitScratch_erase}). The first tape still stores $s$; all work-tape heads now sit at $j+1$, and the output remains empty. These are precisely the scan configuration's defining components at position $j+1$, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_splitPos_read`, `Turing.FinTM.f2_splitPos_succ`, `Turing.FinTM.f2_splitScratch_erase`.
