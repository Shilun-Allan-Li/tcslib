<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldPos_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of folded coordinates

**Claim.** For every integer $z$, its folded coordinate is nonnegative.

**Proof.** If $z\ge 0$, its folded coordinate is $z$, hence nonnegative. If $z<0$, then $-z$ is positive, so $-z-1\ge 0$ for the integer $z$; this is the folded coordinate in that case.
