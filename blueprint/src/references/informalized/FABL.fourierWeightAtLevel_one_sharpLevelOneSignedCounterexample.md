<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.fourierWeightAtLevel_one_sharpLevelOneSignedCounterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Weight of a Linear Function

**Claim.** On the two-dimensional sign cube, the function $g(x_1,x_2)=(x_1+x_2)/2$ has total squared Fourier coefficient $1/2$ on singleton subsets.

**Proof.** The level-one weight is the sum of the squared singleton Fourier coefficients (the level-one expansion, `fourierWeightAtLevel_one_eq_sum_singleton`). For a linear form, the coefficient at the singleton corresponding to coordinate $i$ is its coefficient on that coordinate (`fourierCoeff_linearForm_singleton`). Here both coordinate coefficients are $1/2$, so the level-one weight is $(1/2)^2+(1/2)^2=1/2$.

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.fourierCoeff_linearForm_singleton`.
