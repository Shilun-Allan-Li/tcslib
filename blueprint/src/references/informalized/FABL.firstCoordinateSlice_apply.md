<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.firstCoordinateSlice_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-Coordinate Slice Evaluation

**Claim.** The first-coordinate slice of $f$ at $b$, evaluated at $x$, is $f(b,x)$, where $(b,x)$ is formed by placing $b$ before the coordinates of $x$.

**Proof.** By definition, the slice sends $x$ to the value of $f$ at the vector obtained by adjoining $b$ as its first coordinate. Thus its value at $x$ is exactly $f(\operatorname{cons}(b,x))$.
