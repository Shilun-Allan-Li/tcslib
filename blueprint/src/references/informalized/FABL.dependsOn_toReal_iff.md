<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.dependsOn_toReal_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dependence Under Realification

**Claim.** The real-valued sign version of a Boolean function depends only on a set of coordinates if and only if the sign-valued function itself does.

**Proof.** For the forward implication, take inputs agreeing on the specified coordinates. Dependence of the real-valued version says their output signs have the same real values; injectivity of the sign-to-real map then gives equality of the signs themselves (\texttt{signValue\_injective}). Conversely, equality of the sign-valued outputs implies equality of their real values by applying the sign-to-real map. These are exactly the two dependence assertions.

**Key facts.** `FABL.signValue_injective`.
