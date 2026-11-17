<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.SafeSegment.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Safe Segments

**Claim.** If a run is a safe segment relative to $F$ and $P$, then it is a safe segment relative to $F'$ and $P'$ whenever $F'\subseteq F$ and $P$ implies $P'$ pointwise.

**Proof.** A safe segment contains a segment relative to $F$ and $P$, together with the fact that its endpoint avoids $F$. The segment monotonicity result preserves the same run and endpoint when the forbidden set is reduced from $F$ to $F'$ and the position predicate is weakened from $P$ to $P'$ (`Turing.Segment.mono`). For the endpoint condition, if the endpoint state is outside $F$, it is also outside the subset $F'$. These two facts give the required safe segment.

**Key facts.** `Turing.Segment.mono`.
