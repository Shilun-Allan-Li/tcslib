<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.shStep_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift Step on a Nonempty Gate List

**Claim.** One shift step on the paired unary prefix and encoding of a nonempty gate list removes its first gate from that list and appends the gate, with references shifted by the prefix length, to the output.

**Proof.** First note that unary natural-number encodings satisfy $\operatorname{encodeNat}(j+m)=1^m\,\operatorname{encodeNat}(j)$: both sides consist of $m+j$ ones followed by the terminating zero. Now split according to the constructor of the first gate: variable, constant one, addition, subtraction, or multiplication. In each case, decoding the nested pairing recovers the unary prefix and the encoded gate list. The head and remainder transducers read the gate's tag and its unary-encoded indices; the identities for these transducers on natural-number encodings (`Complexity.BinArith.uHead_encodeNat` and `Complexity.BinArith.uRest_encodeNat`) ensure that the indices are recovered and the remaining gate-list encoding is retained. For arithmetic gates, the displayed encoding identity shifts each referenced index by $m$; for variables and the constant, the encoding is unaffected by shifting. Thus the step returns the original unary prefix, the encoding of the tail gate list, and the output extended by the shifted first gate.

**Key facts.** `Complexity.BinArith.uHead_encodeNat`, `Complexity.BinArith.uRest_encodeNat`.
