<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean :: johnson_lindenstrauss_dist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance Bounds for a Johnson–Lindenstrauss Map

**Claim.** Under the given dimension hypothesis, there exists a linear map whose distances on every pair in $V$ are bounded between $\sqrt{1-\varepsilon}$ and $\sqrt{1+\varepsilon}$ times the original distance.

**Proof.** The Johnson–Lindenstrauss existence theorem supplies a linear map with the squared-distance distortion bounds for all pairs in $V$ (`johnson_lindenstrauss`). Apply the conversion from squared-distance bounds to ordinary norm bounds (`jl_dist_of_embedding`) to that map. It yields the stated lower and upper distance inequalities for every pair.

**Key facts.** `johnson_lindenstrauss`, `jl_dist_of_embedding`.
