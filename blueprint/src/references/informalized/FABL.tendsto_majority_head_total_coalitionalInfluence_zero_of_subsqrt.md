<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majority_head_total_coalitionalInfluence_zero_of_subsqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing majority head influence

**Claim.** If the outside dimension tends to infinity and the head size divided by the square root of the total dimension tends to zero, then the total coalitional influence of the majority head tends to zero.

**Proof.** Apply the total-influence limit theorem with $t=0$; its hypotheses are exactly the assumed divergence of the outside dimension and convergence of the normalized head size to zero (`tendsto_majority_head_total_coalitionalInfluence_totalDimension`). At zero, the standard Gaussian upper tail is $1/2$ (`standardGaussianUpperTail_zero`), so the limiting expression $2(\tfrac12-Q(0))$ is zero. Substituting this value gives the claimed convergence.

**Key facts.** `FABL.tendsto_majority_head_total_coalitionalInfluence_totalDimension`, `FABL.standardGaussianUpperTail_zero`.
