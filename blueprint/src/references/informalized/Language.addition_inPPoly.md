<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/AdderLanguage.lean :: Language.addition_inPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-size circuits for addition

**Claim.** The language of Boolean-word encodings of addition is recognized by well-formed acyclic fan-in-two circuits of polynomial size.

**Proof.** The addition language has fan-in-two circuits of size at most $6n+4$ at input length $n$ (`Language.addition_inSIZE`). This linear bound is at most $6(n+1)$, so the general implication from a size bound dominated by $a(n+1)^k$ to polynomial size, applied with $a=6$ and $k=1$, gives the claim.

**Key facts.** `Language.addition_inSIZE`, `Language.InSIZE.inPPoly`.
