<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.first_evenMoment_condition_redundant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First even moment from the second moment

**Claim.** For positive $r$, if the second moment of $X$ under the given probability mass function is $1$, then its moment of order $2\cdot1$ equals the specified first even-moment bound.

**Proof.** The moment of order $2\cdot1$ is exactly the second moment, so it equals $1$ by hypothesis. The first even-moment bound is also $1$ when $r>0$ (`sharpEvenMomentBound_one`). Substituting this value gives the claimed equality.

**Key facts.** `FABL.sharpEvenMomentBound_one`.
