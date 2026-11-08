<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.succ_le_two_pow_log -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Logarithm Bound

**Claim.** For every natural number $n$, if $k=\mathrm{Nat.log}\,2\,n$ (with the natural logarithm convention at zero), then $n+1\le 2^{k+1}$.

**Proof.** The natural logarithm floor bound gives $n<2^{\mathrm{Nat.log}\,2\,n+1}$ whenever the base is greater than one (`Nat.lt_pow_succ_log_self`). Taking the base to be $2$ yields $n<2^{\mathrm{Nat.log}\,2\,n+1}$. Since both sides are natural numbers, this strict inequality is equivalent to $n+1\le 2^{\mathrm{Nat.log}\,2\,n+1}$, as required.
