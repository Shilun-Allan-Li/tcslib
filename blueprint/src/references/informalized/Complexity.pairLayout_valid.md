<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.pairLayout_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of the pair layout

**Claim.** For any natural numbers $n$, $a$, and $w$, every bit source in the pair layout for lengths $n$ and $a$ is valid with $n+a$ input bits, block width $w$, and instruction index $0$.

**Proof.** Each source in the layout is either an input source from the first range, a constant delimiter, or an input source from the second range. For an index $i<n$, its two repeated input sources satisfy $i<n+a$. The delimiter constants are valid without further conditions. For an index $j<a$ in the second range, its input index is $n+j<n+a$. There are no block sources in the layout, so every listed source is valid.
