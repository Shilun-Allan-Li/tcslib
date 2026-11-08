<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5InputFragment_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Input-Fragment Reconstruction

**Claim.** For the stated time bound, the input fragment extracted at time $t$ from the packed encoding of $x$ with cursor $j$ equals the serialized input clause group at time $t$ for the all-false reference input of length $n+C(n+1)^e$, where $n=|x|$.

**Proof.** Unfold the extracted input fragment and the reference input group so that both are expressed in terms of their input positions and input sizes. The exact-position result (`clA5InputPos_exact`), applicable because $t$ satisfies the assumed horizon bound, identifies the packed encoding’s position with the position in the reference run. The packed-data result (`clA5Data_exact`) identifies its encoded input size with the reference size $n+C(n+1)^e$. Consequently, both constructions make the same decision about whether the position is inside the input and, in either branch, use the same input-group parameters. Their serialized fragments are therefore equal.

**Key facts.** `Complexity.clA5InputPos_exact`, `Complexity.clA5Data_exact`.
