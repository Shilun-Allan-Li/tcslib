<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EdgeIsoperimetric.lean :: FABL.BooleanFunction.toReal_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation of the real representation

**Claim.** For a sign-valued Boolean function $f$, the real-valued representation of its pointwise negation is the pointwise negative of the real-valued representation of $f$.

**Proof.** Fix an input $x$ and evaluate both functions there. Since $f(x)$ is a unit integer, it is either $1$ or $-1$. In either case, converting the negated unit to its real value gives the negative of the real value of the original unit. Thus the two functions agree at every input, so they are equal.
