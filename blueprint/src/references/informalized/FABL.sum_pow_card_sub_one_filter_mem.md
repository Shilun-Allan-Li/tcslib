<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.sum_pow_card_sub_one_filter_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Sum over Subsets Containing a Coordinate

**Claim.** For $\rho\in\mathbb R$ and a coordinate $i$ among the $n$ coordinates, the sum of $\rho^{|S|-1}$ over all subsets $S$ containing $i$ equals $(1+\rho)^{n-1}$.

**Proof.** Replace each subset $S$ containing $i$ by the subset $T=S\setminus\{i\}$ of the other coordinates. This is a bijection, and $|S|-1=|T|$, so the sum becomes the sum of $\rho^{|T|}$ over all subsets of the coordinates other than $i$. Expand $(\rho+1)^{n-1}$ by choosing, for each of those $n-1$ coordinates, either a factor $\rho$ (when it belongs to $T$) or a factor $1$ (when it does not). The resulting terms are precisely $\rho^{|T|}$, proving the identity.
