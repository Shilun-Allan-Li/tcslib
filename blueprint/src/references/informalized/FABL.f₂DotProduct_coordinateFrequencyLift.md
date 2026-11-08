<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBiasMarginals.lean :: FABL.f₂DotProduct_coordinateFrequencyLift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dot product of a lifted coordinate frequency

**Claim.** For a coordinate set $J$, a binary vector $\gamma$ indexed by $J$, and a binary vector $x$ indexed by all $n$ coordinates, the dot product of the coordinate frequency lift of $\gamma$ with $x$ equals the dot product of $\gamma$ with the restriction of $x$ to $J$.

**Proof.** The dot-product pairing identifies a vector with its associated linear functional. By definition, the lifted frequency is the vector corresponding to the functional obtained by composing the functional of $\gamma$ with the coordinate projection onto $J$. Evaluating at $x$ therefore gives the functional of $\gamma$ evaluated at the projection of $x$, which is precisely the claimed dot product.
