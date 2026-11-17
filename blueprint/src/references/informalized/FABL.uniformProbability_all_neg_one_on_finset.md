<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.uniformProbability_all_neg_one_on_finset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of negative signs on prescribed coordinates

**Claim.** For a uniform sign vector in $\{-1,1\}^n$, the probability that every coordinate in $J$ equals $-1$ is $2^{-|J|}$.

**Proof.** Split the sign vector into its coordinates in $J$ and its remaining coordinates. Under this bijective decomposition, the event depends only on the coordinates in $J$, so averaging over the remaining coordinates contributes no change. Among assignments to the $|J|$ coordinates in $J$, exactly one—the assignment that is identically $-1$—satisfies the event. There are $2^{|J|}$ assignments in total, hence the probability is $1/2^{|J|}=((2)^{|J|})^{-1}$.
