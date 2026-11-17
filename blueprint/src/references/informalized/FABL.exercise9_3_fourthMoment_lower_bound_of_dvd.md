<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.exercise9_3_fourthMoment_lower_bound_of_dvd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth moment bound for divisible degrees

**Claim.** If $3\mid k$ and $2k\le n$, the stated six-block multinomial coefficient for $d=k/3$, divided by $\binom{n}{k}^2$, times $(\mathbb{E}F^2)^2$ is at most $\mathbb{E}F^4$ for the level-$k$ polynomial.

**Proof.** Set $d=k/3$. Divisibility gives $3d=k$, and hence $6d=2k\le n$. Apply the fourth moment lower bound for degree $3d$ ($\texttt{exercise9\_3\_fourthMoment\_lower\_bound}$) with this $d$. Replacing each occurrence of $3d$ by $k$ gives the asserted inequality.

**Key facts.** `FABL.exercise9_3_fourthMoment_lower_bound`.
