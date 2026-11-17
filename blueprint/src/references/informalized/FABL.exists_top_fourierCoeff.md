<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.exists_top_fourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A maximal-degree Fourier coefficient

**Claim.** If the Fourier degree of a real-valued function on the sign cube is nonzero, some nonzero Fourier coefficient is indexed by a set whose cardinality equals that degree.

**Proof.** The nonzero degree implies that the Fourier support is nonempty: if it were empty, its supremum of set cardinalities would be zero. Since the support is a finite set and is nonempty, its cardinality function attains its supremum at some member $S$ (the finite-supremum attainment property, `Finset.exists_mem_eq_sup`). By the characterization of Fourier support membership (`mem_fourierSupport`), the coefficient indexed by $S$ is nonzero. The attained supremum says precisely that $|S|$ is the Fourier degree.

**Key facts.** `FABL.mem_fourierSupport`.
