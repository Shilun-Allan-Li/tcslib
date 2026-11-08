<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.binaryCubeComplement_involutive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involution of the Binary-Cube Complement

**Claim.** Applying the binary-cube complement twice to any binary vector returns the original vector.

**Proof.** Compare the two vectors coordinatewise. At each coordinate, complementing twice adds the bit-flip value twice. In the field with two elements this double addition is zero, so associativity and cancellation leave the original coordinate. Since this holds at every coordinate, the vectors are equal.
