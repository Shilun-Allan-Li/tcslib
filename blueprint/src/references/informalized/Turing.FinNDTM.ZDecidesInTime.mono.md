<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHosts.lean :: Turing.FinNDTM.ZDecidesInTime.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of time bounds

**Claim.** If the machine satisfies the total nonhalting probability bound and correct-output condition for $T_1$, and $T_1(n)\le T_2(n)$ for all $n$, then it satisfies both conditions for $T_2$.

**Proof.** Fix an input $x$. For every finite range of horizons, the sum of nonhalting probabilities is at most $T_1(|x|)$ by hypothesis. Since $T_1(|x|)\le T_2(|x|)$, the same sum is at most $T_2(|x|)$. The condition on the output of each halted run is unchanged, so it holds for $T_2$ as well.
