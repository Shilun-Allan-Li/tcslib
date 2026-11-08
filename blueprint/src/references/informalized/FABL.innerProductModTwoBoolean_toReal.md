<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.innerProductModTwoBoolean_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Representation of the Inner Product Function

**Claim.** For every natural number $n$, the real-valued version of the sign-valued inner product Boolean function equals the function obtained by transporting the real sign-encoded inner product from the binary cube to the sign cube.

**Proof.** Evaluate both functions at an arbitrary sign-cube point. By definition, the left side first applies the Boolean function and then takes the real value of its sign. The right side first converts the point back to the binary cube and evaluates the real sign-encoded inner product there. Unfolding these definitions gives the same sign encoding of the same inner product bit, followed by the same real-value map. Thus the functions agree at every point.
