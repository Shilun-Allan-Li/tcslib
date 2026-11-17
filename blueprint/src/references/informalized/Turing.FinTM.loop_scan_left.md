<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loop_scan_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated Scan Reaches Its Exit

**Claim.** If each configuration $c_{j+1}$ steps to $c_j$ for $j<n$, and $c_0$ steps to $d$, then for every $j\le n$, a run of $j+1$ steps from $c_j$ ends at $d$.

**Proof.** Use induction on $n$, proving the assertion for all $j\le n$. At $n=0$, the only choice is $j=0$, and the one-step run ends at $d$ by the exit hypothesis. For the successor case, the new endpoint $j+1$ is handled by taking its first step: the run identity expresses its $(j+2)$-step run as a $j+1$-step run from the result of that first step. Since $j<n+1$, the step hypothesis identifies that result with $c_j$. The induction hypothesis then gives $d$. The remaining indices are covered by the induction hypothesis directly, since they are at most $n$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`.
