<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_baseB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Base Test

**Claim.** The Boolean base test, which accepts when the two specified slices agree or the encoded data certify a valid machine step, is polynomial-time computable.

**Proof.** The two slice offsets are polynomial-time computable: use the offset construction with parameters $(3,1)$ and $(3,2)$, respectively (`pt_vwid_lin`). Applying the block-slice result gives both slices in polynomial time (`pt_blkAt`), and comparing them produces the one-bit equality test in polynomial time (`pt_eq`). For the other disjunct, compute the two configuration slices using `pt_cpAt`, compute the radius bits using `pt_bits_vrad`, and combine them with the extracted input using the pairing construction (`polyTimeComputable_pairFstD`, `PolyTimeComputable.pairEncode`). The valid-step language lies in logspace, so its indicator is polynomial-time computable (`stepLang_mem`, `pt_indicator`); composing it with this encoding gives the second test (`PolyTimeComputable.comp`). Finally, the Boolean disjunction of two polynomial-time one-bit tests is polynomial-time computable (`polyTimeComputable_or`), which is the base test.

**Key facts.** `Complexity.TQBFHard.pt_vwid_lin`, `Complexity.TQBFHard.pt_blkAt`, `Complexity.TQBFHard.pt_eq`, `Complexity.TQBFHard.pt_cpAt`, `Complexity.TQBFHard.pt_bits_vrad`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.Codec.stepLang_mem`, `Complexity.TQBFHard.pt_indicator`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_or`.
