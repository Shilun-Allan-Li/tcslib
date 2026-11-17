<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.AdjScan.lang_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Decidability of Circuit Scan Languages

**Claim.** If a polynomially length-bounded function encodes the circuits of a family on unary inputs, and its output-bit and output-length index languages are decidable in logarithmic space, then each circuit scan language for size, vertex type, or edge queries is decidable in logarithmic space.

**Proof.** Write $f$'s output-length bound and the logarithmic-space decider for its output-bit index language as supplied by the implicit-logspace-computability hypothesis. The proof first handles malformed queries and valid queries separately. A malformed query is rejected immediately by the scan's validity check; the validity characterization (`valid_of_mem`) ensures that any query belonging to the language is valid, so this rejection agrees with the language indicator. The machine's space bound in this case is immediate.

For a valid query, unpack its unary input length and its canonical binary payload. The canonical-bits identity (`canon_eq_bits`) supplies the natural indices represented by the payload. For an edge query this yields indices $iv,tv$ and the target condition for the paired payload; for size and type queries it yields the target vertex index (the auxiliary input index is taken to be zero). The plain-payload and paired-payload decoding identities (`plainWord_pairEncode`, `pairWords_pairEncode`) verify these target conditions and identify the payload with the scan's intended word.

The oracle used by the scan is the indicator of the output-bit index language of $f$. On a unary input of length $n$, querying position $p$ therefore returns the $p$th bit of $f(1^n)$. The index-language pairing identity (`pairEncode_mem_indexLang`) makes this precise, and the circuit-encoding hypothesis identifies $f(1^n)$ with the encoding of the $n$th circuit. Thus the oracle answers the bits of that circuit encoding, with false beyond its end. The scan-halting theorem (`scan_halts`) now gives a bounded halting computation on every valid query. The answer identification theorem (`answer_eq`) equates its task-specific answer with membership in the desired circuit language.

Finally, the scan's space control property for valid inputs (`preS_scan`) and the polynomial output-length bound transfer the register bound to a polynomial in the original query length. In this estimate, encoding the unary input doubles its length and adds the fixed pair separator (`pairEncode_eq_dbl`, `length_dbl`); elementary arithmetic then supplies the polynomial bound required by the general logspace theorem for oracle register machines (`arm_decides_poly`). This proves membership in logarithmic space for the chosen task.

**Key facts.** `Complexity.LogProg.arm_decides_poly`, `BoolCircuit.AdjScan.valid_of_mem`, `Complexity.LogProg.canon_eq_bits`, `Complexity.LogProg.pairWords_pairEncode`, `Complexity.LogProg.plainWord_pairEncode`, `BoolCircuit.AdjScan.pairEncode_mem_indexLang`, `BoolCircuit.AdjScan.scan_halts`, `BoolCircuit.AdjScan.answer_eq`, `BoolCircuit.AdjScan.preS_scan`, `Turing.pairEncode_eq_dbl`, `Turing.length_dbl`.
