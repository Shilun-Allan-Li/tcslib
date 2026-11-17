<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.minimumPositiveAtom_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Minimum Positive Mass

**Claim.** For a probability mass function on a finite set, the smallest mass among points with positive mass is strictly positive.

**Proof.** By the definition of the minimum positive atom, it is the infimum of the real masses $(p(x)).toReal$ over the positive support. For each point $x$ in that support, $p(x)\ne 0$; also, a probability mass is finite. The real-valued mass is therefore strictly positive, by the positivity criterion for the real conversion of a nonzero finite nonnegative real number. Since this holds for every point of the support, the infimum over that finite nonempty support is strictly positive.
