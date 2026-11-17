<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_accB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Acceptance Bit

**Claim.** The function that outputs the one-bit acceptance indicator for the extracted input and configuration data is polynomial-time computable.

**Proof.** First produce a word of true bits whose length is twice the offset $vwid(A,a,|x|)$: the linear-offset construction gives this polynomial-time output by specializing its parameters (`pt_vwid_lin`). The configuration-slice theorem then gives, in polynomial time, the slice beginning at that offset (`pt_cpAt`). Pair this slice with the binary representation of the radius, which is polynomial-time computable (`pt_bits_vrad`), and pair the result with the extracted first component, itself polynomial-time computable (`polyTimeComputable_pairFstD`, `PolyTimeComputable.pairEncode`). This builds exactly the encoded input and configuration data tested by the acceptance language. Since that language is in logspace, its indicator is polynomial-time computable (`acceptLang_mem`, `pt_indicator`). Composing this test with the encoding yields the required one-bit function (`PolyTimeComputable.comp`).

**Key facts.** `Complexity.TQBFHard.pt_vwid_lin`, `Complexity.TQBFHard.pt_cpAt`, `Complexity.TQBFHard.pt_bits_vrad`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.Codec.acceptLang_mem`, `Complexity.TQBFHard.pt_indicator`, `Complexity.PolyTimeComputable.comp`.
