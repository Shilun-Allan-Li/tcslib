<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.product_stableInfluence_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp stable-influence estimate

**Claim.** Under the stated atom-mass, exponent, and rate assumptions, the stable influence satisfies \(\rho I_i^{(\rho)}(f)\le I_i(f)^{2-2/q}\) for every Boolean function and coordinate.

**Proof.** The assumed bound \(\rho\le r_q(\lambda)^2\), together with the positivity of the sharp radius, implies \(\sqrt{\rho}\le r_q(\lambda)\). Apply sharp product hypercontractivity at rate \(\sqrt{\rho}\) to the coordinate Laplacian of \(f\); its norm inequality supplies precisely the contraction hypothesis needed for the stable-influence estimate. Since \(q>2\) also gives \(q\ge2\), that estimate applies and yields \(\rho I_i^{(\rho)}(f)\le I_i(f)^{2-2/q}\).

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_pos_lt_one`, `BooleanAnalysis.Hypercontractivity.product_hypercontractivity_sharp`, `BooleanAnalysis.Hypercontractivity.product_stableInfluence_le_of_norm_noise_laplacian_le`.
