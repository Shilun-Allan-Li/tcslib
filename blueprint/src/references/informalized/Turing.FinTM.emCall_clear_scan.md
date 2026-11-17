<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_clear_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward Erasure Pass

**Claim.** For every $j\le m$, after $j$ steps the cleaner is in state $1$ at $\ell+j$, with both data and marker tapes erased on $[\ell,\ell+j)$ and unchanged elsewhere, and the origin marker unchanged.

**Proof.** Induct on $j$. At $j=0$, the erased interval is empty, so `emCall_cleared_zero` identifies each cleared-tape description with its initial tape; the starting configuration is therefore exactly the claimed one. For the successor step, the marker at the current head position $\ell+j$ is true, since $j<m$. The cleaner in state $1$ erases the symbol at that position on both the data and marker tapes, moves one cell right, and remains in state $1$. The identity `emCall_cleared_step` identifies each updated tape with the tape obtained by extending the erased interval by one cell. The origin tape is not changed, and all heads move together to $\ell+j+1$; the input head does not move (`moveInputPos_zero`). The induction hypothesis and the run decomposition `runFrom_succ_eq_step'` establish the claim for $j+1$.

**Key facts.** `Turing.FinTM.emCall_cleared_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.emCall_cleared_step`, `Turing.moveInputPos_zero`.
