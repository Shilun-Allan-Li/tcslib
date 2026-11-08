<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: Language.inLayeredPPoly_of_le_allOnes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Size Circuits for All-Ones Sublanguages

**Claim.** If every word in a Boolean language consists entirely of true bits, then the language is recognized by a family of layered circuits using identity, NOT, and unbounded fan-in AND gates, with polynomially bounded size.

**Proof.** The two-node construction theorem provides a family of layered circuits using only the allowed gates, of size at most $2$ at every input length, whose recognized language is $L$ (`Language.inLayeredSIZE_two_of_le_allOnes`). A constant size bound is polynomial: take $a=2$ and $k=0$, so $2\leq 2(n+1)^0$ for every $n$. The general conversion from a size bound dominated by $a(n+1)^k$ to polynomial layered size then gives the result (`Language.InLayeredSIZE.inLayeredPPoly`).

**Key facts.** `Language.inLayeredSIZE_two_of_le_allOnes`, `Language.InLayeredSIZE.inLayeredPPoly`.
