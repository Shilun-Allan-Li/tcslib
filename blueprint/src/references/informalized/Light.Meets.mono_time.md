<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Calls.lean :: Light.Meets.mono_time -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increasing the Cost Bound

**Claim.** If a call meets cost bound $T$ with postcondition $R$ and $T\le T'$, then it meets cost bound $T'$ with the same postcondition.

**Proof.** Apply monotonicity of calls (`Light.Meets.mono`) using $T\le T'$ and the implication from $R$ to itself. The execution and its final state are unchanged; only the allowed cost bound is enlarged.

**Key facts.** `Light.Meets.mono`.
