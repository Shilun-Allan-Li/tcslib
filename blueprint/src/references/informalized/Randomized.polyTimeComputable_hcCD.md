<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.polyTimeComputable_hcCD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Coin Construction

**Claim.** The function that retains the $1$ bits of the decoded second component, pairs them with the fourfold length-limited iteration output from the decoded first component, and applies the unary multiplication construction is polynomial-time computable.

**Proof.** The map extracting the decoded second component and retaining its $1$ bits is polynomial-time computable, as is the map taking the decoded first component to the fourfold length-limited iteration output. Pairing these two outputs is polynomial-time computable by closure under pair encoding. The unary multiplication construction is polynomial-time computable, and composing it with this paired-output map proves the result.

**Key facts.** `Randomized.polyTimeComputable_onesW_snd`, `Randomized.polyTimeComputable_hlDWord`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_mulU`, `Complexity.BinArith.polyTimeComputable_app`.
