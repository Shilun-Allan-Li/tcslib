<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CoordRestriction.completeSign_negateAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion commutes with sign negation

**Claim.** Negating the fixed signs of a restriction and negating the input vector before completion produces the coordinatewise negation of the original completion.

**Proof.** Check each coordinate by cases on its state in ρ. A free coordinate remains free after negating the restriction, so its completed value is the negated input coordinate, which is the negative of its original completed value. A coordinate fixed at $1$ becomes fixed at $-1$, and completion returns $-1$, the negative of the original value $1$. A coordinate fixed at $-1$ becomes fixed at $1$, and completion returns $1$, the negative of the original value $-1$. Thus the two vectors agree at every coordinate.
