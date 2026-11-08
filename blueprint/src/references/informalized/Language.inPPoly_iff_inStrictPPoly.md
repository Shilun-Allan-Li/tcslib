<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: Language.inPPoly_iff_inStrictPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict and Unrestricted Polynomial Size

**Claim.** For every Boolean language, polynomial-size recognition by fan-in-two circuits is equivalent to polynomial-size recognition by a family that is fan-in-two at length zero and, at every positive length, has distinct gate inputs, the prescribed exact arities, and every non-output vertex feeding some gate.

**Proof.** Given a polynomial-size family with bound $a(n+1)^k$, the conversion theorem `Language.InSIZE.inStrictSIZE` produces an equivalent strict family with size bounded by $4a(n+1)^k+12$. Since $(n+1)^k\ge1$, this is at most $(4a+12)(n+1)^k$, so the same exponent and a larger coefficient establish strict polynomial size. Conversely, `Language.InStrictSIZE.inSIZE` forgets the additional strictness conditions while retaining fan-in at most two, the size bound, and the recognized language. Thus strict and unrestricted polynomial size coincide.

**Key facts.** `Language.InSIZE.inStrictSIZE`, `Language.InStrictSIZE.mono`, `Language.InStrictSIZE.inSIZE`.
