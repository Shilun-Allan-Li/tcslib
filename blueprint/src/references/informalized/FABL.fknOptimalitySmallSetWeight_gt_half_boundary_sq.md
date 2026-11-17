<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalitySmallSetWeight_gt_half_boundary_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for Level-One Fourier Weight

**Claim.** For each natural number $q$, the selected upper-tail set has level-one Fourier weight greater than half the square of the Gaussian density at the threshold.

**Proof.** Let $W$ be the level-one Fourier weight and $b$ the Gaussian boundary. The approximation gives $|W-b^2|<b^2/2$, hence $b^2-W<b^2/2$. Rearranging yields $W>b^2/2$.

**Key facts.** `FABL.fknOptimalitySmallSetWeight_approx`.
