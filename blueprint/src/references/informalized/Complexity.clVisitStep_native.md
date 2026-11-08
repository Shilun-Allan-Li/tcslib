<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitStep_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time producer step

**Claim.** For every finite-state binary Turing machine $M$ and natural numbers $C,e$, the producer-step function on Boolean words is polynomial-time computable.

**Proof.** Construct the next time header by appending one true bit to the decoded time field; this is polynomial-time, using the polynomial-time header extraction and append operations, with the constant one-bit function computable in linear time. Construct the request for the new row by pairing the decoded input field with the decoded time field. The visit-row function is polynomial-time, and composing it with this request remains polynomial-time. Finally, assemble the output by pairing the input header with the updated time header and the old tail followed by the new row. Header extraction, tail extraction, pairing, and append are polynomial-time operations, so the full producer-step function is polynomial-time.

**Key facts.** `Complexity.clHeaderField_native`, `Turing.FinTM.computesFunInTime_const`, `Complexity.clNative_linear`, `Complexity.clNative_append`, `Complexity.clNative_pair`, `Complexity.clVisitRow_native`, `Complexity.clHeaderTail_native`.
