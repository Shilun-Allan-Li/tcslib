<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncHash.lean :: CommunicationComplexity.Functions.Hash.collisionPiece_measureReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure of a collision piece

**Claim.** For distinct inputs $x,y$ and a hash value $a$, the set of hash functions taking both inputs to $a$ has measure $(1/k)^2$.

**Proof.** View the collision piece as a product box in the space of hash functions: its allowed coordinate values are $\{a\}$ at $x$ and $y$, and all of $\{\mathrm{Fin}\,k\}$ at every other coordinate. The measure of this box is the product of the coordinate measures (\texttt{measureReal\_pi\_univ}). Since $x\ne y$, removing these two coordinates leaves only unrestricted coordinates, each of measure $1$; the two constrained coordinates each have singleton measure $1/k$ (\texttt{hashRange\_singleton\_measureReal}). Multiplying gives $(1/k)^2$.

**Key facts.** `CommunicationComplexity.FiniteProbabilitySpace.measureReal_pi_univ`, `CommunicationComplexity.Functions.Hash.hashRange_singleton_measureReal`.
