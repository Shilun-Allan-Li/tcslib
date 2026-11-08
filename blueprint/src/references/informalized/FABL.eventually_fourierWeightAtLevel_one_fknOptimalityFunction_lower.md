<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.eventually_fourierWeightAtLevel_one_fknOptimalityFunction_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Modified Function Fourier Weight

**Claim.** For all sufficiently large integers $q$, the level-one Fourier weight of the real-valued version of the modified Boolean function is at least $1-\Delta_q+\frac{1}{36}\Delta_q^2\log(1/\Delta_q)$, where $\Delta_q$ is twice the uniform mass of the small set.

**Proof.** Eventually the small-set indicator has level-one Fourier weight at least $\frac{1}{36}\Delta_q^2\log(1/\Delta_q)$. The exact identity for the modified function expresses its level-one Fourier weight as $1-\Delta_q+\Delta_q^2/4$ plus the small-set indicator's level-one weight. Substituting the eventual lower bound gives the desired estimate, since $\Delta_q^2/4\ge 0$.

**Key facts.** `FABL.eventually_fknOptimalityGain`, `FABL.fourierWeightAtLevel_one_fknOptimalityFunction_eq_delta`.
