<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedNoiseExtensions.lean :: FABL.uniformExtendedCoordinateNoisePMF_apply_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of extended coordinate noise

**Claim.** For the extended coordinate-noise distribution in the stated parameter range, the probability assigned to moving from $x$ to $y$ equals that assigned to moving from $y$ to $x$.

**Proof.** The proof converts both probability masses to their real-valued forms; this is valid because probability masses are finite and hence are not infinite. In that form, the mass depends only on whether the two points coincide: when $x=y$ it is the common diagonal value, and when $x\ne y$ it is the common off-diagonal value. The condition $x=y$ is symmetric in the two points, so exchanging $x$ and $y$ leaves the mass unchanged. Therefore the two probability masses agree.
