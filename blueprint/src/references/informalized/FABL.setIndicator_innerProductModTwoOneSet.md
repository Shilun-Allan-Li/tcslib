<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.setIndicator_innerProductModTwoOneSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator of the Inner-Product-One Set

**Claim.** The indicator of the set where the inner product modulo two equals $1$ is the real-valued function that is $1$ when that inner product equals $1$ and $0$ otherwise.

**Proof.** Evaluate both functions at an arbitrary vector $z$. The inner product modulo two is either $0$ or $1$ (`f₂_eq_zero_or_one`). If it is $1$, then $z$ belongs to the set and the real embedding has value $1$, so the two values agree. If it is $0$, then $z$ is outside the set and the real embedding has value $0$, so again the values agree. Thus the functions are equal at every vector.

**Key facts.** `FABL.f₂_eq_zero_or_one`.
