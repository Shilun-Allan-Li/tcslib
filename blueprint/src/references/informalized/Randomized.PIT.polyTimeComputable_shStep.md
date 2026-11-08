<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.polyTimeComputable_shStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Shift Step

**Claim.** The function updating a bit-string configuration by leaving it unchanged when its word is done, and otherwise re-encoding its context, remaining word, and shifted gate data, is polynomial-time computable.

**Proof.** Extracting the word component is polynomial-time computable, by the result for the second nested projection (Complexity.BinArith.polyTimeComputable_slot2). Composing this extraction with the done test and with the remaining-word function gives polynomial-time tests and data for the update. In the non-done case, the output pairs the first projection of the configuration with a second encoding: its first component is the remaining word, and its second component concatenates the third projection with the shifted gate word. The third projection is polynomial-time computable (Complexity.BinArith.polyTimeComputable_slot3); the shifted gate word is polynomial-time computable by composing the gate-shifting result with the first projection and extracted word, and concatenation and pair encoding preserve polynomial-time computability. Finally, the polynomial-time conditional closure combines the identity output in the done case with this encoded output otherwise.

**Key facts.** `Complexity.BinArith.polyTimeComputable_slot2`, `Randomized.PIT.polyTimeComputable_isDone`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.pairEncode`, `Randomized.PIT.polyTimeComputable_restW`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.PolyTimeComputable.append`, `Randomized.PIT.polyTimeComputable_shiftGateW`, `Complexity.polyTimeComputable_ite`.
