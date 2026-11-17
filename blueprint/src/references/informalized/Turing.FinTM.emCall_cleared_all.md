<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_cleared_all -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Entire Marked Interval

**Claim.** If a tape is blank outside $[\ell,\ell+m)$, then erasing the first $m$ cells of that interval makes it blank everywhere.

**Proof.** Fix an integer position $z$. If $z$ lies in $[\ell,\ell+m)$, the definition of erasure makes the resulting tape blank at $z$. If it does not lie in that interval, the hypothesis says the original tape was already blank at $z$, and erasure leaves that value unchanged. Thus the erased tape is blank at every position.
