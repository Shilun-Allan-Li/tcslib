<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.fourierCoeff_improvedFKNBalancedLift_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced-lift coefficient after a swap

**Claim.** The Fourier coefficient at coordinate $0$ of the balanced lift after swapping coordinates $0$ and $i+1$ equals the coefficient of $f$ at coordinate $i$.

**Proof.** The real-valued version of the swapped lift is the real-valued balanced lift composed with the coordinate swap (`improvedFKNBalancedLift_toReal`). Fourier coefficients of a function composed with a coordinate permutation transform by applying the inverse permutation to the frequency (`fourierCoeff_comp_permuteInput`). The inverse swap sends the singleton frequency $\{0\}$ to $\{i+1\}$, so the desired coefficient is the balanced lift's coefficient at $\{i+1\}$. The balanced-lift identity (`fourierCoeff_balancedFKNLift_succ'`) identifies this with the coefficient of $f$ at $\{i\}$.

**Key facts.** `FABL.improvedFKNBalancedLift_toReal`, `FABL.fourierCoeff_comp_permuteInput`, `FABL.fourierCoeff_balancedFKNLift_succ'`.
