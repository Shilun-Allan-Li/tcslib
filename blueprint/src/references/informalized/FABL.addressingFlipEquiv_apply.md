<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.addressingFlipEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing flip map

**Claim.** For every $m$ and every sign vector $x$ of length $m+2^m$, the addressing flip map sends $x$ to the vector obtained by flipping the data coordinate selected by the address encoded in the first $m$ coordinates of $x$.

**Proof.** By definition, the addressing flip map sends $x$ to the result of applying the coordinate-flip operation at the selected coordinate. Thus its value is precisely $x$ with the data coordinate chosen by its address part flipped.
