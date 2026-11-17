<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: Language.allOnes_inPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Size for All Ones

**Claim.** The all-ones language is recognized by a family of well-formed acyclic Boolean circuits with fan-in at most two and polynomially bounded size.

**Proof.** Use the established linear-size circuit-family result, which bounds the size at length $n$ by $2n+1$ ( `Language.allOnes_inSIZE_linear`). The general implication from a size bound $T(n)$ to polynomial size applies once $T(n)\le a(n+1)^k$ is verified ( `Language.InSIZE.inPPoly`). Choose $a=3$ and $k=1$: since $2n+1\le 3(n+1)$ for every natural number $n$, the linear bound is dominated by this polynomial.

**Key facts.** `Language.allOnes_inSIZE_linear`, `Language.InSIZE.inPPoly`.
