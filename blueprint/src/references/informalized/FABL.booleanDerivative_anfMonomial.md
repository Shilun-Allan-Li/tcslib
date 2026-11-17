<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/DirectionalDerivatives.lean :: FABL.booleanDerivative_anfMonomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Finite-Field Monomial

**Claim.** The Boolean derivative of the monomial indexed by $S$ in direction $y$ is the sum over proper subsets $T\subsetneq S$ of the product of the monomial on $T$ at $x$ and the monomial on $S\setminus T$ at $y$.

**Proof.** Evaluate both sides at an arbitrary $x$. The derivative is the monomial at $x$ plus its value at $x+y$. Expand the latter using the monomial addition formula (\(\texttt{anfMonomial_add}\)): it is the sum over all subsets $T\subseteq S$ of the monomial on $T$ at $x$ times the monomial on $S\setminus T$ at $y$. The term indexed by $T=S$ is exactly the monomial at $x$, since the monomial on the empty set is $1$. It occurs once in that sum, so adding the initial monomial cancels it in characteristic two. The remaining terms are precisely those indexed by subsets other than $S$, as claimed.

**Key facts.** `FABL.anfMonomial_add`.
