<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.booleanDual_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Boolean Duality

**Claim.** If the Boolean duals of two functions agree at every sign vector, then the functions themselves agree at every sign vector.

**Proof.** Assume the duals of $f$ and $g$ agree everywhere, and fix an arbitrary sign vector $x$. Evaluate their duals at the coordinatewise negation of $x$. Negating that argument returns $x$, so the assumed equality reads $-f(x)=-g(x)$. Cancelling the common negation gives $f(x)=g(x)$. Since $x$ was arbitrary, the functions agree everywhere.
