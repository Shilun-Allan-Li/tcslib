<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.validW_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Valid Circuit Encodings

**Claim.** For every finite bit string $x$, the validity test returns true exactly when $x$ decodes to a well-formed algebraic circuit on some finite number of inputs.

**Proof.** Suppose first that the validity test accepts. Its three Boolean conditions say that $x$ contains a false bit, the scan of its encoded gates finishes successfully, and the scan has processed at least one gate. The scan characterization (`exists_of_runOk`) therefore supplies a gate list whose encoding is the scan input, together with the fact that every gate refers only to earlier gates. The nonempty-scan condition rules out an empty list. Since $x$ contains a false bit, the unary-prefix decomposition theorem (`eq_encodeNat_of_hasFalse`) writes $x$ as the unary encoding of the number of inputs followed by the gate encoding. Thus the resulting circuit has the required well-formedness, and the decode/encode characterization (`decode_eq_some_iff`) shows that it decodes from $x`.

Conversely, suppose $x$ decodes to a well-formed circuit $C$ with $n$ inputs. Decoding determines the exact encoding of $C$ (`encode_of_decode`). The unary prefix forces the scan to recover $n$ and the gate encoding; the gate-run theorem (`gateRun_encodeGates`) says that a well-formed gate list completes the scan successfully. Its nonempty gate list makes the final scan state nonempty. Finally, every unary natural-number encoding contains a false terminator (`hasFalse_encodeNat`), so the three conditions defining the validity test all hold.

**Key facts.** `Randomized.PIT.exists_of_runOk`, `Randomized.PIT.length_evalVals`, `Randomized.PIT.runOk_encState`, `Complexity.BinArith.eq_encodeNat_of_hasFalse`, `Randomized.AlgCircuit.decode_eq_some_iff`, `Randomized.PIT.gateRun_encodeGates`, `Complexity.BinArith.hasFalse_encodeNat`, `Randomized.AlgCircuit.encode_of_decode`, `Randomized.PIT.scan_ctx`.
