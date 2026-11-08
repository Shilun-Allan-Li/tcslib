<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Segment.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of segment conditions

**Claim.** If $F'\subseteq F$ and $P$ implies $P'$ at every work-tape position tuple, then every segment satisfying the conditions for $F$ and $P$ also satisfies them for $F'$ and $P'$.

**Proof.** The run endpoint is unchanged. At each time before the endpoint, the original state lies outside $F$, and hence outside its subset $F'$. At each time through the endpoint, the original position tuple satisfies $P$, so the assumed implication gives $P'$ there.
