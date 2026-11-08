<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Duality.lean :: BooleanAnalysis.GaussianSpace.memLp_and_eLpNorm_le_of_bounded_pairing -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability from bounded pairings

**Claim.** On a probability space, if $q>1$, $u$ is integrable, and all pairings of $u$ with essentially bounded measurable functions are bounded by $C$ times the corresponding $L^{q/(q-1)}$ norm, then $u$ belongs to $L^q$ and its extended $L^q$ norm is at most $C$.

**Proof.** For each natural number $m$, truncate $|u|$ at height $m$, setting $v_m=\min(|u|,m)$. Each truncation is measurable, nonnegative, bounded, and dominated by $|u|$. The bounded-pairing estimate gives the uniform bound $\|v_m\|_q\le C$ (`eLpNorm_le_of_bounded_pairing`). Pointwise, these truncations converge to $|u|$. The lower semicontinuity inequality for extended $L^q$ norms under almost-everywhere limits therefore bounds the norm of $|u|$ by the lower limit of the truncation norms, which is at most $C$. Since $u$ is integrable it is almost everywhere strongly measurable; the finite norm bound then gives membership in $L^q$ as well as the claimed norm estimate.

**Key facts.** `BooleanAnalysis.GaussianSpace.eLpNorm_le_of_bounded_pairing`.
