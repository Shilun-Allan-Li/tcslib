<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_xW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Indexed Circuit Values

**Claim.** For every polynomial-time computable function on bit strings, using its value on a gate-state string as an index to retrieve the corresponding circuit value is polynomial-time computable.

**Proof.** On input $D$, compute $f(D)$ and pair-encode it with the state’s stored value list, extracted as $sL(D)$. The assumed polynomial-time computability of $f$ and polynomial-time computability of $sL$ make this encoding polynomial-time computable. The lookup procedure `getW` is polynomial-time computable, so composing it with the encoded input gives the desired function $D\mapsto xW(f(D),D)$.

**Key facts.** `Randomized.PIT.polyTimeComputable_sL`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_getW`, `Complexity.PolyTimeComputable.comp`.
