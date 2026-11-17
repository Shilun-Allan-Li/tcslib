<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.MatAt.congr_below -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Below an Endpoint

**Claim.** If μ encodes A at the specified indices, μ' agrees with μ below e, and a+nk≤e, then μ' encodes A at those indices as well.

**Proof.** Apply the interval-agreement result `Light.MatAt.congr`. For any index b in its interval, a≤b and b<a+nk≤e, so b<e. The assumed agreement below e therefore gives μ'(b)=μ(b), exactly the agreement required by that result.

**Key facts.** `Light.MatAt.congr`.
