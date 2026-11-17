<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov.lean :: BooleanAnalysis.GaussianSpace.profile_mean_restrictions_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Profile inequality for restricted means

**Claim.** For a function from the Boolean cube of dimension $n+1$ into $[0,1]$, the Gaussian profile of its mean is bounded by the average of the two square-root expressions formed from the profiles of its restrictions and the mean of its last-coordinate difference.

**Proof.** Let $u$ and $v$ be the expectations of the restrictions obtained by fixing the last coordinate to $0$ and $1$, respectively. Since the original function takes values in $[0,1]$, both restricted expectations lie in $[0,1]` (`expect_mem_unitInterval`). The expectation on the full cube is $(u+v)/2$ (`expect_succ_eq`), and the expectation of the half-difference is $(u-v)/2$ (`expect_diffLast`). Apply the two-point profile inequality (`bobkov_two_point`) with $a=(u+v)/2$ and $b=(u-v)/2$. Its two shifted arguments are $u$ and $v$, so its conclusion is precisely the desired bound after substituting these expectation identities.

**Key facts.** `BooleanAnalysis.GaussianSpace.expect_mem_unitInterval`, `BooleanAnalysis.Hypercontractivity.expect_succ_eq`, `BooleanAnalysis.GaussianSpace.expect_diffLast`, `BooleanAnalysis.GaussianSpace.bobkov_two_point`.
