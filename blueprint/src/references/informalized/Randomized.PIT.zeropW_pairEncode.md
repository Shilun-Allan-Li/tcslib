<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.zeropW_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Zero-Test Verifiers

**Claim.** For all finite bit strings $x$ and $r$, the word-level verifier on the paired encoding of $x$ and $r$ equals the circuit-level verifier on $x$ and $r$.

**Proof.** Pair decoding recovers $x$ and $r$, so split into whether the word validity test accepts. If it accepts, the validity characterization (`validW_iff`) gives a well-formed circuit $C$ decoded from $x$. Its encoding recovers the unary input-count prefix and the gate list (`encode_of_decode`, together with the unary-prefix facts `uHead_encodeNat` and `uRest_encodeNat`); the scan-state identity (`sI_scanRun`) supplies the circuit size. The pipe identity (`pipe_eq`) then expresses the word verifier's trials as equality of the two encoded evaluations. One evaluation is zero exactly when the other is zero: the evaluation specification (`evalModW_spec`) identifies the encoded residue with the circuit evaluation, and the bound on that residue permits use of the residue-zero criterion (`natCast_eq_zero_iff_of_lt`). The circuit zero-test characterization (`zeroTest_eq`) identifies this condition with the circuit verifier's test, yielding agreement in this case.

If the validity test rejects, its characterization says there is no well-formed circuit decoding from $x$. The word verifier consequently accepts by its definition. The circuit-level verifier also accepts: if decoding fails it accepts directly, and if decoding succeeds the decoded circuit cannot be well formed, so the verifier accepts by its invalid-circuit branch.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Randomized.PIT.validW_iff`, `Randomized.AlgCircuit.encode_of_decode`, `Complexity.BinArith.uHead_encodeNat`, `Complexity.BinArith.uRest_encodeNat`, `Randomized.PIT.sI_scanRun`, `Randomized.PIT.pipe_eq`, `Randomized.PIT.zeroTest_eq`, `Randomized.PIT.bitsVal_evalModW_nil`, `Randomized.PIT.evalModW_spec`, `Randomized.PIT.natCast_eq_zero_iff_of_lt`.
