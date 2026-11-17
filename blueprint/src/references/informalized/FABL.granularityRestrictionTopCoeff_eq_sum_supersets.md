<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.granularityRestrictionTopCoeff_eq_sum_supersets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction coefficient as a sum of Fourier coefficients

**Claim.** The top restriction coefficient on $J$ equals the sum of the Fourier coefficients indexed by sets $U$ containing $J$.

**Proof.** Expand the sign-valued function in its Fourier expansion at the point obtained by extending an assignment on $J$ by $1$ outside $J$. Multiply the expansion by the full monomial of the assignment and take expectation over assignments on $J$. The monomial of a Fourier index $U$ restricts to the monomial on those indices of $U$ that lie in $J$; this is the restriction identity for monomials. Interchanging the finite sum and expectation, orthogonality of monomials shows that the resulting factor is $1$ exactly when that restricted frequency set is all of $J$, and is $0$ otherwise. The criterion that the restricted set is all of $J$ exactly when $J\subseteq U$ therefore leaves precisely the Fourier coefficients indexed by supersets of $J$. Writing this as a filtered sum gives the claimed identity.

**Key facts.** `FABL.fourier_expansion_from_interpolation`, `FABL.monomial_granularityExtendAtOne`, `FABL.expect_granularityIndexedMonomial_mul`, `FABL.granularityFrequencyWithin_eq_univ_iff`.
