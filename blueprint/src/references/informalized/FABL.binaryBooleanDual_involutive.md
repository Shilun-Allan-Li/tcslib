<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.binaryBooleanDual_involutive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involutivity of Boolean Duality

**Claim.** Taking the Boolean dual twice returns the original function.

**Proof.** Evaluate the double dual at any input $x$. By definition, it is the negative of the dual's value at the coordinatewise complement of $x$. That dual value is itself the negative of $f$ evaluated at the complement of that complement. Complementing twice returns $x$, and negating twice returns the original sign, so the value is $f(x)$. Since this holds for every input, the two functions are equal.
