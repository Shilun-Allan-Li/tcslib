<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.measure_uniformPMF_real_eq_ncard_div_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Measure of a Finite Event

**Claim.** For a finite nonempty measurable space with measurable singletons, the uniform measure of an event $A$ is its cardinality divided by the cardinality of the whole space.

**Proof.** The uniform measure assigns mass $1/|\Omega|$ to each point. Expanding the measure of $A$ as the sum of the point masses gives one such contribution for each $x\in A$, and zero for each point outside $A$. Thus the sum is $|A|/|\Omega|$. In the proof, the finite-set cardinality is identified with the cardinality of the corresponding set of points, and the real-valued mass $1/|\Omega|$ is multiplied by the number of those points.
