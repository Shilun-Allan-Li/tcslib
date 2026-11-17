<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.fourierWeightOutside_antitone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Exterior Fourier Weight

**Claim.** If $A\subseteq B$, then the sum of squared Fourier coefficients over coordinate sets outside $B$ is at most the corresponding sum over sets outside $A$.

**Proof.** Every set outside $B$ is also outside $A$: if it belonged to $A$, the inclusion $A\subseteq B$ would put it in $B$. Thus the indexing family for the exterior weight of $B$ is contained in the indexing family for the exterior weight of $A$. Each summand is nonnegative because it is a squared Fourier coefficient. Summing over the smaller family therefore gives no more than summing over the larger one.
