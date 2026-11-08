<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.SafeSegment.endpoint_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safe Segment Endpoint Avoidance

**Claim.** If a segment is safe, then its endpoint's state lies outside the forbidden set.

**Proof.** By definition, a safe segment consists of a segment together with the assertion that the endpoint state lies outside the forbidden set. The desired conclusion is exactly this second assertion.
