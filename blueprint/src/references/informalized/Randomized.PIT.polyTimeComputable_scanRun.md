<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_scanRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Scan Run

**Claim.** The scan-run function on a bit string is polynomial-time computable.

**Proof.** First, the input encoding is polynomial-time computable: the unary head and unary rest are polynomial-time computable, the inner fixed pair is constant, and the two pair encodings preserve polynomial-time computability. The closure of polynomial-time functions under pair encoding gives this conclusion. The scan run is exactly the gate-run function applied to that encoding. Since gate run is polynomial-time computable, closure under composition proves the result.

**Key facts.** `Complexity.BinArith.polyTimeComputable_uHead`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_uRest`, `Randomized.PIT.polyTimeComputable_gateRun`, `Complexity.PolyTimeComputable.comp`.
