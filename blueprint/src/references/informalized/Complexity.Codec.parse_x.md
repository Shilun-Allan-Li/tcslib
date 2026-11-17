<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.parse_x -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired Input Parsing

**Claim.** For any finite bit string $y$, either $y=\langle x,r\rangle$ for some bit strings $x,r$, and the program in the specified mode reaches its first parsing-test stage with all earlier registers bounded by $(8W+8)(|y|+1)$, or $y$ has no pair representation and the program halts false with the same register bound.

**Proof.** Let $B=(8W+8)(|y|+1)$. The length bound gives $|y|\le B$, so the initial length scan can fill the length register and reach the first parser stage with all registers bounded (`length_le_bnd`, `len_run`). The parser-run result (`pr_run`), applied at pointer zero, divides the proof according to whether the pairing decoder succeeds on $y$.

If decoding fails, the parser reaches rejection. A pair representation would decode successfully, since decoding an encoded pair recovers its components (`pairDecode_pairEncode`); thus no pair representation exists. The bounded rejection result (`halt_rej`) converts this run into a false halt, with the updated pointer still within the register bound.

If decoding succeeds with components $x,r$, the decoder characterization (`eq_pairEncode_of_pairDecode`) gives $y=\langle x,r\rangle$. The parser has then advanced its pointer by $2|x|+2$, and its registers agree with the claimed values up to that point. The copy routine (`cp_run`) copies this pointer into the first-component-length register: its destination is initially zero and therefore no larger than its source. Its endpoint is the first parsing-test stage with the specified register values. The bounded length scan, parser run, and copy run concatenate to give the required reachability; arithmetic using the encoded-pair length formula (`length_pairEncode`) verifies the pointer bound and the register values. The register-bound invariant supplies the required bound throughout the concatenated run.

**Key facts.** `Complexity.Codec.length_le_bnd`, `Complexity.Codec.len_run`, `Complexity.Codec.pr_run`, `Turing.pairDecode_pairEncode`, `Complexity.Codec.halt_rej`, `Complexity.Codec.Reach.trans`, `Turing.eq_pairEncode_of_pairDecode`, `Complexity.Codec.Reach.cast`, `Complexity.Codec.cp_run`, `Turing.length_pairEncode`.
