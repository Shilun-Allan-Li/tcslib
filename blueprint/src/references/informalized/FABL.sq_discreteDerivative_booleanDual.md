<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.sq_discreteDerivative_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative Squares Under Boolean Duality

**Claim.** For a Boolean sign function $f$, its Boolean dual has coordinate derivative whose square at $x$ equals the square of the derivative of $f$ at the negated point.

**Proof.** Expand each discrete derivative as half the difference between the function values with coordinate $i$ set to $1$ and to $-1$ (`discreteDerivative_apply`). Negating the input with coordinate $i$ set to $1$ gives the negation of $x$ with that coordinate set to $-1$; likewise, negating the input with coordinate $i$ set to $-1$ gives the negation of $x$ with that coordinate set to $1$. Thus the two evaluations in the dual derivative are the two evaluations of $f$ at the negated point, in reversed order, with an additional minus sign from the definition of the dual. The sign-value map carries negation to real negation (`signValue_neg`). Consequently the resulting derivative agrees with the derivative of $f$ at the negated point up to an overall sign. Squaring removes that sign, proving the equality.

**Key facts.** `FABL.discreteDerivative_apply`, `FABL.signValue_neg`.
