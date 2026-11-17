<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: Language.allOnes_inLayeredPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial layered circuits for all-ones words

**Claim.** The language of Boolean words whose entries are all true is recognized by finite-layer circuits using identity, NOT, and unbounded fan-in AND gates, with polynomially bounded size.

**Proof.** A layered circuit family recognizes the all-ones language with size at most $n+1$ at input length $n$ (`Language.allOnes_inLayeredSIZE_linear`). Since $n+1\le 1\cdot(n+1)^1$, the general size-bound implication yields polynomial layered size, with the same allowed gate operations and recognized language.

**Key facts.** `Language.allOnes_inLayeredSIZE_linear`, `Language.InLayeredSIZE.inLayeredPPoly`.
