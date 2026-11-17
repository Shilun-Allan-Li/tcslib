<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.finrank_real_fun_eq_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension of a finite function space

**Claim.** For a finite set $\Omega$, the real vector space of functions on $\Omega$ has dimension $|\Omega|$.

**Proof.** The indicator functions of the individual points of $\Omega$ form the standard coordinate basis of the function space: each is nonzero, distinct point indicators have disjoint support and are linearly independent, and every function is their linear combination with coefficients given by its pointwise values. Hence the dimension is the number of points in $\Omega$.
