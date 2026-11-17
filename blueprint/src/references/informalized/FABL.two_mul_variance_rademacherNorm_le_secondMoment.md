<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KhintchineKahane.lean :: FABL.two_mul_variance_rademacherNorm_le_secondMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rademacher norm variance bound

**Claim.** For vectors \(w_1,\ldots,w_n\) in a real normed vector space, twice the variance of the Rademacher sum's norm is at most the second moment of that norm.

**Proof.** The Rademacher norm is even under simultaneous sign reversal (\(\texttt{FABL.rademacherNorm_even}\)), so the variance-versus-total-influence inequality for even functions gives \(2\operatorname{Var}(g)\le I(g)\) (\(\texttt{FABL.two_mul_variance_le_totalInfluence_of_even}\)). Total influence is the uniform inner product of \(g\) with its Laplacian (\(\texttt{FABL.uniformInner_laplacian_eq_totalInfluence}\)). Pointwise, the Laplacian of this norm is at most the norm itself (\(\texttt{FABL.laplacian_rademacherNorm_le}\)); multiplying by the nonnegative norm preserves the inequality. Averaging yields \(I(g)\le \mathbb E[g^2]\), and combining the bounds gives the claim.

**Key facts.** `FABL.rademacherNorm_even`, `FABL.two_mul_variance_le_totalInfluence_of_even`, `FABL.uniformInner_laplacian_eq_totalInfluence`, `FABL.laplacian_rademacherNorm_le`.
