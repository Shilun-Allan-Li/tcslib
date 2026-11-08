<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.booleanInfluence_eq_two_mul_negOnePivotal_probability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence and negative pivotal probability

**Claim.** For a Boolean function and a coordinate, its influence is twice the probability that the function is $-1$ and pivotal in that coordinate.

**Proof.** Fix the coordinate and partition the pivotal inputs into those where $f(x)=-1$ and those where $f(x)=1$. These two sets are disjoint and together contain every pivotal input, since the function takes only the values $-1$ and $1$. Flipping the chosen coordinate is an involution (`flipCoordinate_flipCoordinate`) and preserves pivotality. Moreover, it exchanges the two parts: if a pivotal input has value $-1$, its flipped input must have value $1$, and conversely. Thus the two parts have equal cardinality, so the total number of pivotal inputs is twice the number in the negative part. On the finite uniform cube, each event's probability is its cardinality divided by the cube size. Substituting the cardinality relation gives the asserted identity.

**Key facts.** `FABL.flipCoordinate_flipCoordinate`.
