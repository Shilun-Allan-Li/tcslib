<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.influence_innerProductModTwoBoolean_eq_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of the binary inner-product function

**Claim.** For every positive integer $m$, the influence of the binary inner-product sign function at each of its $2m$ coordinates is $1/2$.

**Proof.** Express the influence as the sum of squared Fourier coefficients over subsets $S$ containing the chosen coordinate $i$ (\texttt{FABL.influence_eq_sum_sq_fourierCoeff}). Every such coefficient has absolute value $2^{-m}$ (\texttt{FABL.abs_fourierCoeff_innerProductModTwoBoolean}), so its square is $2^{-2m}$. The number of subsets containing $i$, counted with the weight appearing in the proof, is evaluated by the subset-sum identity $\sum_{S\ni i}\rho^{|S|-1}=(1+\rho)^{2m-1}$ (\texttt{FABL.sum_pow_card_sub_one_filter_mem}) at $\rho=1$. Thus the influence is $2^{2m-1}\cdot 2^{-2m}=1/2$.

**Key facts.** `FABL.influence_eq_sum_sq_fourierCoeff`, `FABL.abs_fourierCoeff_innerProductModTwoBoolean`, `FABL.sum_pow_card_sub_one_filter_mem`.
