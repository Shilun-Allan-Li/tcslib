<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean :: Complexity.size_le_logSpace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Size Bound

**Claim.** For every natural number $n$, its binary size satisfies $\operatorname{size}(n)\le \log_2(n)+1$.

**Proof.** The characterization of binary size reduces the desired inequality to a strict bound of the form $n<2^{\operatorname{log}_2(n)+1}$ (`Nat.size_le`). The base $2$ is greater than $1$, so the standard logarithm bound gives this strict power inequality (`Nat.lt_pow_succ_log_self`). Since the quantities are integers, the strict bound yields the asserted weak inequality.
