<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.exercise9_3_fourthMoment_lower_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth moment lower bound

**Claim.** When $6d\le n$, the stated multinomial coefficient divided by $\binom{n}{3d}^2$, multiplied by $(\mathbb{E}F^2)^2$, is at most $\mathbb{E}F^4$ for the level-$3d$ polynomial $F$.

**Proof.** The second moment identity for a level-$k$ polynomial is $\mathbb{E}F_k^2=\binom{n}{k}$ ($\texttt{expect\_levelKPolynomial\_sq}$). Here $k=3d$, and $\binom{n}{3d}>0$ because $3d\le n$. Substituting the identity into the left side cancels the squared binomial denominator, leaving the six-block multinomial coefficient. The fourth moment estimate for this polynomial says that this coefficient is at most $\mathbb{E}F^4$ ($\texttt{sixBlockMultinomial\_le\_fourthMoment\_levelKPolynomial}$), proving the claim.

**Key facts.** `FABL.expect_levelKPolynomial_sq`, `FABL.sixBlockMultinomial_le_fourthMoment_levelKPolynomial`.
