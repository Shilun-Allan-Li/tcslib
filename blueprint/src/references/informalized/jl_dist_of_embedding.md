<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean :: jl_dist_of_embedding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared and Unsquared Distance Bounds

**Claim.** If a linear map satisfies the two-sided squared-distance distortion bounds on every pair in a finite set, then its distances on those pairs lie between the corresponding square-root-scaled original distances.

**Proof.** Fix $u,v$ in the set and apply the assumed distortion bounds to this pair. Since $0<\varepsilon<1$, both $1-\varepsilon$ and $1+\varepsilon$ are nonnegative. All norms are nonnegative as well. For the lower bound, take square roots in $(1-\varepsilon)\|u-v\|^2\le\|f(u)-f(v)\|^2$. The square root of a squared norm is the norm itself, and the square root of the left side factors as $\sqrt{1-\varepsilon}\,\|u-v\|$. For the upper bound, take square roots in $\|f(u)-f(v)\|^2\le(1+\varepsilon)\|u-v\|^2$ and factor the right side in the same way. This proves both distance inequalities for each pair.
