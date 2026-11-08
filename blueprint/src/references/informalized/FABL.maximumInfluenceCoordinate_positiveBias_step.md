<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.maximumInfluenceCoordinate_positiveBias_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-bias coordinate step

**Claim.** For a monotone Boolean function with positive bias strictly below one and at least two coordinates, fixing a maximum-influence coordinate to $1$ increases its positive bias by at least $2p(1-p)\,\mathrm{briberyRate}(n)$, where $p$ is its original positive bias.

**Proof.** Let $i$ be the chosen maximum-influence coordinate. The variance identity gives $\operatorname{Var}(f)=4p(1-p)>0$. By the KKL bound, this variance times $\log n/(100n)$ is at most the maximum coordinate influence. Monotonicity identifies the influence at coordinate $i$ with the singleton Fourier coefficient. The mean under fixing coordinate $i$ to $1$ equals the original mean plus that coefficient; converting means to positive biases therefore shows that the new bias is $p+\tfrac12\mathrm{MaxInf}[f]$. Finally, substitute the KKL lower bound and the definition of the bribery rate, and rearrange, to obtain the asserted increase.

**Key facts.** `FABL.variance_eq_four_mul_positiveBias`, `FABL.kkl`, `FABL.booleanInfluence_maximumInfluenceCoordinate`, `FABL.mean_fixCoordinate_one`, `FABL.influence_eq_fourierCoeff_singleton_of_monotone`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.positiveBias_eq_mean`.

**Caveat.** The supplied informal statement also describes an iterative asymptotic bribery bound; this proof establishes the single-step inequality only.
