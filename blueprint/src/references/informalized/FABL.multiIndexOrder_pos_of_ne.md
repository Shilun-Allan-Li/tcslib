<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.multiIndexOrder_pos_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive order from a nonzero coordinate

**Claim.** If some coordinate $i$ satisfies $a(i)\ne z$, then the number of coordinates $j$ with $a(j)\ne z$ is positive.

**Proof.** The support consists of exactly those coordinates where $a$ differs from $z$. The hypothesis places $i$ in this support, so it is nonempty. A nonempty finite set has positive cardinality; hence the order of $a$ is positive.
