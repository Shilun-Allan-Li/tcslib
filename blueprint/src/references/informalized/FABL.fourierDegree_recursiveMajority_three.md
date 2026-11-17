<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.fourierDegree_recursiveMajority_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of recursive majority

**Claim.** For every depth $d$, the real-valued recursive majority function on three-input gates has Fourier degree exactly $3^d$.

**Proof.** The function acts on $3^d$ coordinates, so its Fourier degree is at most $3^d$ (`fourierDegree_le_dimension`). For the reverse inequality, suppose its degree were smaller. Since degrees are natural numbers, it would then be at most $3^d-1$. The Fourier degree criterion would force the coefficient on the full coordinate set to vanish, because that set has size $3^d$. But this full-set coefficient equals the recursively defined top coefficient (`fourierCoeff_recursiveMajorityThree_univ_eq_addressTopCoeff`), which is nonzero (`addressRecursiveMajorityThreeTopCoeff_ne_zero`). This contradiction proves the lower bound and hence equality.

**Key facts.** `FABL.fourierDegree_le_dimension`, `FABL.fourierDegree_le_iff`, `FABL.fourierCoeff_recursiveMajorityThree_univ_eq_addressTopCoeff`, `FABL.addressRecursiveMajorityThreeTopCoeff_ne_zero`.
