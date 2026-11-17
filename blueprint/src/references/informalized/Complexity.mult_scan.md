<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired-String Scan

**Claim.** Under the stated register bound, endpoint condition, and bit-alignment hypothesis, the program reaches the false-answer state if parsing $w$ fails, with register $0$ advanced by at most $|w|$. If parsing returns $(a,\_)$, it reaches the copy state indexed by $b$ with register $0$ advanced by $2|a|+2$. Safety holds at every earlier step.

**Proof.** The loop follows the paired-string parser through the bits of $w$. Its scan register advances in the given stride, and the alignment hypothesis identifies each oracle bit query with the corresponding bit of $w$; the oracle’s bit-query specification (`mult_queries`) supplies those answers. The aligned-pair loop theorem (`alignedPair_loop`) therefore gives the run and its safety invariant. If the parser fails, the theorem records the bounded scan position at which the program rejects. If parsing succeeds with first component $a$, it records the endpoint after that component and its separator, namely an advance of $2|a|+2$.

**Key facts.** `Complexity.LogProg.alignedPair_loop`, `Complexity.mult_queries`.
