<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Interpolation.lean :: FABL.forall_coordinate_eq_iff_eq_zero_or_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant binary vectors

**Claim.** When $n>0$, a vector in $(\mathbb F_2)^n$ has all coordinates equal exactly when it is the zero vector or the all-one vector.

**Proof.** Choose coordinate $0$, which exists because $n>0$. If all coordinates are equal and the value at coordinate $0$ is $0$, then every coordinate is $0$, so the vector is zero. Otherwise its value at coordinate $0$ is nonzero; in the two-element field the only such value is $1$, and equality of all coordinates makes the vector all ones. Conversely, both the zero vector and the all-one vector have equal values at every pair of coordinates.
