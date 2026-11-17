<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Rotation.lean :: BooleanAnalysis.GaussianSpace.rotationSensitivity_tendsto_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of Rotation Sensitivity at Zero

**Claim.** For measurable $A\subseteq\mathbb R^n$, the rotation sensitivity of $A$ tends to zero as the angle tends to zero.

**Proof.** Let $\mu$ be the joint law of two independent standard Gaussian vectors, and let $E$ be the event that the first vector lies in $A$. For each angle $u$, write $f(u)$ for the rotation acting on the pair. This map varies continuously with $u$, and every such rotation preserves $\mu$ (measurePreserving_gaussianRotation). The symmetric difference of $f(u)^{-1}(E)$ and $f(0)^{-1}(E)$ is precisely the event that membership in $A$ differs between the first vector and its rotated first coordinate. The measure of this symmetric difference therefore equals the rotation sensitivity. Continuity of measure under continuously varying preimages at the identity implies that this measure tends to zero as $u\to0$. Since the measures are finite, applying continuity of the conversion from extended nonnegative reals to reals at zero gives the asserted real-valued limit.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianRotation`.
