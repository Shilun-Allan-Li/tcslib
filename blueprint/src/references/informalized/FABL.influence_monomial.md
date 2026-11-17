<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/Basic.lean :: FABL.influence_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of a monomial

**Claim.** For a monomial indexed by $S$, its influence at coordinate $i$ is $1$ if $i\in S$ and $0$ otherwise.

**Proof.** If $i\in S$, the discrete derivative of the monomial is the monomial with $i$ removed (\texttt{FABL.discreteDerivative_monomial}). That monomial squares to $1$ everywhere (\texttt{FABL.monomial_sq}), so the squared derivative is constantly $1$ and its expectation is $1$. If $i\notin S$, the discrete derivative is identically zero by the same derivative formula, so its square and expectation are zero. The two cases give the stated indicator value.

**Key facts.** `FABL.discreteDerivative_monomial`, `FABL.monomial_sq`.
