<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitRestore_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cleanup Scan Configurations

**Claim.** For every $j\le |s|$, after $j$ steps from the initial scan configuration, the cleanup machine is in the scan configuration at count $j$, with its input head at the saturated position, the first tape still storing $s$, scratch tapes cleared in their first $j$ cells, and all work heads at displacement $j$.

**Proof.** Use induction on $j$. At $j=0$ the run has not moved, so the claim is exactly the initial scan configuration. For the successor step, the induction hypothesis identifies the current scan configuration, and its first work tape reads $s[j]=1$ because $j<|s|$. The input-position reading fact `splitPos_read` identifies the input symbol: it is a symbol when $j<|w|$ and blank at the boundary or beyond. The state-$0$ transition advances the input head and all work heads by one, leaves the first tape unchanged, and blanks the scratch cell at position $j$. The position update is precisely the next saturated scan position (`splitPos_succ`), and the scratch tape after erasing that cell is the scratch tape with its first $j+1$ cells cleared (`splitScratch_erase`). Finally, the state flag is updated from $|w|<j$ to $|w|<j+1$: the input-reading fact distinguishes whether the scan is still within $w$ or has reached its blank boundary. These updates give exactly the scan configuration at count $j+1$, using the successor-time run identity (`runFrom_succ_eq_step'`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.splitPos_read`, `Turing.FinTM.splitPos_succ`, `Turing.FinTM.splitScratch_erase`.
