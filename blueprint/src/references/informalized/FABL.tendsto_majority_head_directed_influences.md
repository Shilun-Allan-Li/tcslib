<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majority_head_directed_influences -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Directed Majority Influence Limits

**Claim.** If $m(q)\to\infty$ and $k(q)/\sqrt{m(q)}\to t$, then the influence of the first $k(q)$ coordinates toward either output of majority tends to the stated Gaussian limit.

**Proof.** 1. Since $k(q)+m(q)\ge m(q)$, the total dimension tends to infinity. The threshold limits then give three convergences: the plus-bribe threshold tends to $-t$ (`tendsto_majorityPlusBribeThreshold`), the minus-bribe threshold tends to $t$ (`tendsto_majorityMinusBribeThreshold`), and the baseline threshold $-1/\sqrt{k(q)+m(q)}$ tends to $0$ (`tendsto_majorityBaselineThreshold`).

2. The limiting theorem for expected upper-tail indicators says that, when the dimension diverges and the threshold converges to $a$, the corresponding expectations tend to the standard Gaussian upper tail at $a$ (`tendsto_expect_hammingUpperTailIndicator_of_tendsto`). Applying it to the plus-bribe, minus-bribe, and baseline thresholds gives respective limits $\Pr[Z>-t]$, $\Pr[Z>t]$, and $\Pr[Z>0]$, where $Z$ is standard Gaussian.

3. The exact formula for influence toward $1$ is the plus-bribe expectation minus the baseline expectation (`coalitionalInfluenceToward_majority_head_one`); the formula toward $-1$ is the baseline expectation minus the minus-bribe expectation (`coalitionalInfluenceToward_majority_head_neg_one`). Taking limits of these differences gives $\Pr[Z>-t]-\Pr[Z>0]$ and $\Pr[Z>0]-\Pr[Z>t]$. Gaussian symmetry gives $\Pr[Z>-t]=1-\Pr[Z>t]$ (`standardGaussianUpperTail_neg`), and symmetry about zero gives $\Pr[Z>0]=1/2$ (`standardGaussianUpperTail_zero`). Both differences therefore equal $1/2-\Pr[Z>t]$, the stated Gaussian limit.

**Key facts.** `FABL.tendsto_majorityPlusBribeThreshold`, `FABL.tendsto_majorityMinusBribeThreshold`, `FABL.tendsto_majorityBaselineThreshold`, `FABL.tendsto_expect_hammingUpperTailIndicator_of_tendsto`, `FABL.standardGaussianUpperTail_neg`, `FABL.standardGaussianUpperTail_zero`, `FABL.coalitionalInfluenceToward_majority_head_one`, `FABL.coalitionalInfluenceToward_majority_head_neg_one`.
