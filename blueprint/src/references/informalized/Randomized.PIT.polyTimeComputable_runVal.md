<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_runVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Bit-String Transformation

**Claim.** The transformation $R$ that forms the specified encoded pair from the input projections and then applies the bounded second-projection iteration is polynomial-time computable.

**Proof.** The input projection $sI$ is polynomial-time computable, and dropping its first bit is also polynomial-time computable; composing these operations gives polynomial-time computability of $D\mapsto (sI(D)).drop\,1$. The length projection $sL$ is polynomial-time computable as well. Pairing these two outputs with the bit-string pair encoding preserves polynomial-time computability (`PolyTimeComputable.pairEncode`). Finally, `getW` is polynomial-time computable, so composing it with this encoded-pair transformation remains polynomial-time computable (`PolyTimeComputable.comp`). By the definition of $R$, this composite is precisely the desired transformation.

**Key facts.** `Complexity.polyTimeComputable_tail`, `Randomized.PIT.polyTimeComputable_sI`, `Complexity.PolyTimeComputable.comp`, `Randomized.PIT.polyTimeComputable_sL`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_getW`, `Complexity.PolyTimeComputable.comp`.
