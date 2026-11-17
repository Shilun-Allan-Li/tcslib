<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Calls.lean :: Light.Meets.mono_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling the Cost Bound

**Claim.** If a call meets cost bound $cS$ with postcondition $R$ and $c\le c'$, then it meets cost bound $c'S$ with the same postcondition.

**Proof.** Since $S$ is a natural number, multiplication preserves the order in its left factor, so $cS\le c'S$. Apply cost-bound monotonicity (`Light.Meets.mono_time`) with this inequality, retaining the same postcondition $R.

**Key facts.** `Light.Meets.mono_time`.
