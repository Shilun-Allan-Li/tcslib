<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluenceToward_tribes_block_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes Influence Toward Negative One

**Claim.** For the tribes function on $s$ blocks of width $w$, the coalitional influence of any one block toward $-1$ is $(1-2^{-w})^s$.

**Proof.** The tribes function is monotone (`tribes_monotone`), so its influence toward $-1$ is half the decrease in its mean after bribing the selected block to $-1$ (`coalitionalInfluenceToward_neg_one_eq_mean_change`). Bribing that entire block makes the tribes function constantly $-1$ (`bribeFunction_tribes_block_neg_one`), whose mean is therefore $-1$. The mean of the tribes function equals its empty-set Fourier coefficient (`mean_eq_fourierCoeff_empty`), and that coefficient is $2(1-2^{-w})^s-1$ (`fourierCoeff_tribes_empty`). Substituting these two means into the half-difference gives $(1-2^{-w})^s$.

**Key facts.** `FABL.tribes_monotone`, `FABL.coalitionalInfluenceToward_neg_one_eq_mean_change`, `FABL.bribeFunction_tribes_block_neg_one`, `FABL.mean_eq_fourierCoeff_empty`, `FABL.fourierCoeff_tribes_empty`.
