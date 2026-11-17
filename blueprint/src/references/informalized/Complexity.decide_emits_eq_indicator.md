<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableauCorrect.lean :: Complexity.decide_emits_eq_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission Detects the Language Indicator

**Claim.** If $M$ decides $L$ within time $T$, then on every input $x$ the Boolean decision that some time $s<T(|x|)$ has a selected transition emitting $1$ equals the indicator of membership of $x$ in $L$.

**Proof.** Apply the result for a machine that computes a single bit to the computation supplied by the decision hypothesis at input $x$. Its output bit is the language indicator of $x$, and the single-bit emission characterization states that the decision based on emissions before the time bound equals that bit (`decide_emits_eq_of_computesInTime`).

**Key facts.** `Complexity.decide_emits_eq_of_computesInTime`.
