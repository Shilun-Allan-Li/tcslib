<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.InAC.inPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# AC languages have polynomial circuit size

**Claim.** If a language has a well-formed polynomial-size AC circuit family with polylogarithmic depth, then it has a fan-in-two circuit family whose size is bounded by $a(n+1)^k$ for some natural numbers $a$ and $k$.

**Proof.** The hypothesis gives an AC depth exponent $d$. By the AC-to-NC conversion, the language has a fan-in-two NC family (`Language.InAC.inNC_succ`). Every such NC family has polynomial size in the stated sense (`Language.InNC.inPPoly`), yielding the required constants $a$ and $k$.

**Key facts.** `Language.InAC.inNC_succ`, `Language.InNC.inPPoly`.
