<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/ArrowLevelOneBound.lean :: FABL.exists_levelOneWeight_upperError_isLittleO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic level-one Fourier weight bound

**Claim.** For any sequence of Boolean functions with equal singleton Fourier coefficients at each dimension, the level-one Fourier weight is eventually at most $2/\pi+r(n)$ for some error $r(n)$ tending to zero.

**Proof.** Choose $r(n)=3/n$, which tends to zero (`three_div_nat_isLittleO_one`). For every $n\ge1$, the equal-singleton-coefficient estimate (`fourierWeightAtLevel_one_le_two_div_pi_add_three_div_card`) gives level-one weight at most $2/\pi+3/n$. Since the positive integers are eventually at least one, this proves the asserted eventual inequality.

**Key facts.** `FABL.three_div_nat_isLittleO_one`, `FABL.fourierWeightAtLevel_one_le_two_div_pi_add_three_div_card`.
