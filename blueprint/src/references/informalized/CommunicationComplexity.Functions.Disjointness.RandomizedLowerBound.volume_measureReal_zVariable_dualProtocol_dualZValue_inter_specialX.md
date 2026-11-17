<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_zVariable_dualProtocol_dualZValue_inter_specialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual Special-Bit Fiber Volume

**Claim.** For each achievable statistic value and bit $b$, the dual fiber restricted to samples whose special Alice bit is $b$ has the same real-valued volume as the original fiber restricted to samples whose special Bob bit is $b$.

**Proof.** The proof first uses the equality of the corresponding extended volumes, supplied by the special-bit fiber volume identity (`volume_zVariable_dualProtocol_dualZValue_inter_specialX`). Applying the real-valued measure operation to both sides gives the asserted equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_zVariable_dualProtocol_dualZValue_inter_specialX`.
