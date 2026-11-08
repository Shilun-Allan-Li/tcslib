<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.CNFFormula.booleanDual_involutive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involution of Boolean duality

**Claim.** For a Boolean function on the sign cube, applying Boolean duality twice returns the original function.

**Proof.** To prove the two functions equal, fix an input $x$. The double dual evaluates $f$ at the coordinatewise negation of the coordinatewise negation of $x$, and negates the output twice. Since each sign is its own double negation, both operations cancel, giving $f(x)$. This holds for every input, so the functions are equal.
