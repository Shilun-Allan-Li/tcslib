<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.frontier_gaussianDisagreementRegion_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary of the Disagreement Region

**Claim.** Every point on the frontier of the region where the product of the two coordinates is negative has at least one coordinate equal to zero.

**Proof.** For continuous real-valued functions $f$ and $g$, the frontier of the strict sublevel set $\{z:f(z)<g(z)\}$ lies in the equality set $\{z:f(z)=g(z)\}$; apply this frontier principle (`frontier_lt_subset_eq`) to the product of the coordinates and the constant zero function. At a point on this frontier, the product is therefore zero. A product of real numbers is zero only if at least one factor is zero, which gives the stated union of coordinate axes.
