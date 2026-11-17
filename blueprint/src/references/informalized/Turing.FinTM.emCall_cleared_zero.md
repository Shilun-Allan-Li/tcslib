<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_cleared_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Erasures Change Nothing

**Claim.** For every data tape $d$ and integer $\ell$, erasing the cells in the empty interval $[\ell,\ell)$ leaves $d$ unchanged.

**Proof.** At any cell $z$, the condition $\ell\le z<\ell+0$ is impossible. The erasure therefore selects the original tape value at every cell, so the two tapes are equal.
