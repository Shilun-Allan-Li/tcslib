<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersInner_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor-Dimensional Inner Product Decomposition

**Claim.** The Gowers inner product in dimension $k+1$ equals the average over $y$ of the product of the half expectations obtained by fixing the last coordinate to $0$ and to $1$.

**Proof.** Apply the coordinate-splitting identity (FABL.gowersInner_split_at) with the coordinate chosen to be the last one. By definition, the half expectation at the last coordinate is the half expectation denoted without an explicit coordinate in the statement. Substituting this notation gives the asserted decomposition.

**Key facts.** `FABL.gowersInner_split_at`.
