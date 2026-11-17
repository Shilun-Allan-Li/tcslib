<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.rademacherMeasure_eq_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product structure of the Rademacher measure

**Claim.** The uniform probability measure on the sign cube of dimension $n$ is the product over its coordinates of the uniform probability measure on the two-point sign space.

**Proof.** The sign cube is the function space from the finite index set of $n$ coordinates to the sign space. The uniform measure on a finite function space is the product of the uniform measures on each coordinate (`uniformSample_toMeasure_eq_pi`). Applying that identity to the sign space gives the stated equality.

**Key facts.** `FABL.uniformSample_toMeasure_eq_pi`.
