<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.zeroTest_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Test Characterization

**Claim.** The circuit zero-test on $r$ equals the proposition that every specified trial evaluates the circuit to zero at the point and modulo determined by the corresponding blocks of $r$.

**Proof.** The proof first identifies the input blocks. For each input coordinate, the corresponding block of the truncated random string lies entirely within the input section; list truncation therefore gives the same block as taking it directly from $r$. By the definitions of the test point and the point-list, their encoded values agree. It next identifies the modulus blocks: for every trial index in range, the corresponding block lies within the remaining section of the truncated string, so the same list identity (`take_drop_take`) makes its value agree with the block taken directly from $r$. After these identifications, the circuit-level test and the displayed universal condition quantify over the same trial indices. Each direction follows by translating an index between the finite trial range and the inequality-bounded range, and replacing the point and modulus using the two block identities.

**Key facts.** `Randomized.PIT.take_drop_take`.
