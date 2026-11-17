<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.parityTimes_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real form of parity multiplication

**Claim.** For a set $S$ of coordinates and a Boolean function $g$, the real-valued function associated with their pointwise product is the pointwise product of the monomial on $S$ and the real-valued function associated with $g$.

**Proof.** Prove equality of the two functions by fixing an input $x$. The real-valued form of the parity function on $S$ is the monomial on $S$ (FABL.parityFunction_toReal). Thus the real value of the pointwise product is the product of that monomial with the real value of $g$. The sign values involved are signs, so their integer multiplication agrees with multiplication after viewing them as real numbers; this gives the asserted pointwise identity.

**Key facts.** `FABL.parityFunction_toReal`.
