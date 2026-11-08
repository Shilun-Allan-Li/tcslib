<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/AlgebraicDegree.lean :: FABL.algebraicDegree_anfMul_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for ANF multiplication

**Claim.** The algebraic degree of the product defined by union-indexed coefficient convolution is at most the sum of the degrees of its factors.

**Proof.** By the support characterization of degree ($\texttt{algebraicDegree_le_iff}$), take a subset $U$ whose product coefficient is nonzero. This coefficient is a finite sum of terms indexed by pairs $(S,T)$, and a nonzero finite sum must have a nonzero summand. Thus for some pair, $U=S\cup T$ and $c(S)d(T)\ne0$. Both $c(S)$ and $d(T)$ are nonzero, so $|S|\le\deg(c)$ and $|T|\le\deg(d)$. Since $|S\cup T|\le|S|+|T|$, it follows that $|U|\le\deg(c)+\deg(d)$, as required.

**Key facts.** `FABL.algebraicDegree_le_iff`.
