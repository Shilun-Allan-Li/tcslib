<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.anfMonomial_f₂CubeOfFinset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial on a subset indicator

**Claim.** At the point that is $1$ on $U$ and $0$ outside it, the monomial indexed by $S$ equals $1$ if $S\subseteq U$, and equals $0$ otherwise.

**Proof.** The point's coordinate at $i$ is $1$ precisely when $i\in U$ (`f₂CubeOfFinset_apply`). If $S\subseteq U$, every factor in the product defining the monomial is $1$, so the product is $1$. If $S\not\subseteq U$, choose $i\in S$ with $i\notin U$. The product then contains a zero factor, so it is zero.

**Key facts.** `FABL.f₂CubeOfFinset_apply`.
