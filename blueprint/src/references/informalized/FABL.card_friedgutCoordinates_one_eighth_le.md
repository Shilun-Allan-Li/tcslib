<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LargeFourierCoefficient.lean :: FABL.card_friedgutCoordinates_one_eighth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-eighth Friedgut coordinate bound

**Claim.** When the parameter is $1/8$, the number of Friedgut coordinates is at most $64 I[f]^3 9^{\lceil 8I[f]\rceil}$, provided the total influence $I[f]$ is positive.

**Proof.** Use the general Friedgut coordinate bound (card_friedgutCoordinates_le) with $\varepsilon=1/8$. The degree identity (friedgutDegree_one_eighth) identifies the resulting degree with $\lceil 8I[f]\rceil$. Substituting these values gives a factor $I[f]^3/(1/8)^2=64I[f]^3$ and the stated power of $9$.

**Key facts.** `FABL.card_friedgutCoordinates_le`, `FABL.friedgutDegree_one_eighth`.
