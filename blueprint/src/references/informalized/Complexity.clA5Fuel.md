<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Fuel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomially Bounded Emission Fuel

**Claim.** The last-round function $n\mapsto n+(k+3)T(n)+k+1$, for $T(n)=c\bigl(A(n+C(n+1)^e+1)^d+1\bigr)^2$, is polynomially bounded; moreover, its little-endian binary representation at $n=|x|$ is polynomial-time computable from $x$.

**Proof.** First construct the packed body word with cursor zero. It is polynomial-time computable by composing the polynomial-time packed-record construction with the machine that prepends a fixed pair-encoding prefix (`Complexity.clPackedRecords_native`, `Turing.FinTM.computesFunInTime_pairEncodeFixed`, and `Complexity.clNative_linear`). Computing the stored round count from this packed word is polynomial-time (`Complexity.clA5StoredRound_native`, composed with that packing computation). The exact packing identity `Complexity.clA5Stored_exact` identifies this stored count with $n+(k+3)T(n)+k+1$, giving a polynomial-time machine that outputs the unary word of that length. For the polynomial bound, run this machine on the length-$n$ all-false input. The time characterization `Turing.FinTM.computesInTime_iff` identifies its output with the unary word of the specified length; the machine’s output length is at most its running time (`Turing.MultiTapeTM.output_length_le`). Since the running time has the form $a(n+1)^r$, this bounds the last-round function by a polynomial. Finally, converting a polynomial-time unary output into its binary length representation is polynomial-time: compose the unary computation with the length-to-bits machine (`Turing.FinTM.computesFunInTime_lengthBits`) using `Complexity.PolyTimeComputable.comp`.

**Key facts.** `Complexity.clA5StoredRound_native`, `Complexity.clA5Stored_exact`, `Complexity.clNative_linear`, `Complexity.clPackedRecords_native`, `Turing.FinTM.computesFunInTime_pairEncodeFixed`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.PolyTimeComputable.comp`.
