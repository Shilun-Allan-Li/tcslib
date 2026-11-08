<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.mem_DTIMEAdvice_of_inSIZE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Size Yields Polynomial-Time Advice

**Claim.** If a language has fan-in-two Boolean circuits of size at most $a(n+1)^k$, then it has a polynomial-time advice decider with advice length $(12a^2+1)(n+1)^{2k}$.

**Proof.** From the circuit-family hypothesis, take a family $C$ of fan-in-two circuits representing $L$, with the stated size bound. Encode each circuit as advice. The circuit-encoding bound (`BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo`) gives an encoding of length at most $12$ times the square of its size. Squaring the size bound and using $(n+1)^{2k}\ge 1$ shows that the encoding, with room for the padding marker, fits within $(12a^2+1)(n+1)^{2k}$ bits. Pad each encoding to exactly that length; the padding-length fact (`Complexity.length_padAdvice`) verifies the length.

The decider first processes the input-and-advice encoding to remove the padding and recover the circuit description paired with the input. This preprocessing is polynomial time: stripping the padding is polynomial-time computable (`Turing.FinTM.computesFunInTime_stripLast`), and extracting the input and pairing the results are polynomial-time operations (`Complexity.polyTimeComputable_of_linear`, `Complexity.PolyTimeComputable.pairEncode`). It then runs the circuit evaluator, whose time is quadratic in its encoded input length (`BoolCircuit.CircuitEval.evalTM_computes`). On the correctly padded advice, the recovered description is exactly the circuit for the input length; the pairing and padding identities (`Turing.pairDecode_pairEncode`, `Complexity.splitAtLastTrue_pad`) establish this, and the evaluator returns the language's indicator (`Complexity.verdict_encode_family`).

Finally, the advice and input together have length bounded by a constant times $(n+1)^{2k+1}$. The polynomial time bound in the input length therefore yields a bound of the form $c(n^r+1)$ for some natural exponent $r$ and constant $c$, by the length-to-time estimate (`Complexity.time_le_of_length_le`). Increasing the running-time bound if necessary preserves the computation (`Turing.FinTM.ComputesInTime.mono`), proving the required advice-complexity membership.

**Key facts.** `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo`, `Complexity.length_padAdvice`, `Turing.FinTM.computesFunInTime_stripLast`, `Complexity.polyTimeComputable_of_linear`, `Complexity.PolyTimeComputable.pairEncode`, `BoolCircuit.CircuitEval.evalTM_computes`, `Turing.pairDecode_pairEncode`, `Complexity.splitAtLastTrue_pad`, `Complexity.verdict_encode_family`, `Complexity.time_le_of_length_le`, `Turing.FinTM.ComputesInTime.mono`.
