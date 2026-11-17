<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.parityFunction_eq_parityCountProfile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity from the Positive-Coordinate Count

**Claim.** For a coordinate subset $S$ and sign input $x$, the parity function on $S$ equals $(-1)^{|S|-k}$, where $k$ is the number of coordinates in $S$ at which $x$ equals $1$; the exponent is a natural-number subtraction, hence is truncated at zero.

**Proof.** First use the identity expressing the parity product over $S$ as $(-1)$ raised to the number of coordinates in $S$ where $x$ is negative (parityFunction_eq_neg_one_pow_negativeCoordinateCountOn). The positive- and negative-coordinate counts add to $|S|$ (positiveCoordinateCountOn_add_negativeCoordinateCountOn). Therefore the negative-coordinate count is $|S|$ minus the positive-coordinate count, with natural subtraction. Replacing the exponent by this expression gives the claimed profile formula.

**Key facts.** `FABL.parityFunction_eq_neg_one_pow_negativeCoordinateCountOn`, `FABL.positiveCoordinateCountOn_add_negativeCoordinateCountOn`.
