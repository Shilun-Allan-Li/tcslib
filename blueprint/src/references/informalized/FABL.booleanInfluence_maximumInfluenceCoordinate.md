<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.booleanInfluence_maximumInfluenceCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum-Influence Coordinate

**Claim.** For a Boolean function on a positive-dimensional sign cube, the coordinate selected as a maximum-influence coordinate has influence equal to the maximum influence.

**Proof.** Since the dimension is positive, the existence theorem supplies a coordinate whose influence equals the maximum influence. The selected coordinate is defined by choosing a witness to that existence statement. The defining property of the chosen witness therefore gives the asserted equality.

**Key facts.** `FABL.exists_booleanInfluence_eq_maximumInfluence`.
