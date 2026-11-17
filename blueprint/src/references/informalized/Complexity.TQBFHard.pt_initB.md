<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_initB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Initial-Configuration Test

**Claim.** For every finite nondeterministic Turing machine $N$ and natural numbers $d,c,A,a$, the function sending $y$ to the one-bit result of the specified initial-configuration membership test is polynomial-time computable.

**Proof.** The language of valid initial configuration codes for $N$ is decidable in logarithmic space (`Complexity.Codec.initLang_mem`). Its membership indicator is therefore polynomial-time computable by `pt_indicator`. It remains to produce the tested encoding in polynomial time. The first pair projection of $y$ is polynomial-time computable; the slice beginning at offset $\mathrm{vwid}(A,a,|x|)$ is polynomial-time computable by `pt_cpAt`, using the polynomial-time unary encoding of that offset supplied by `pt_vwid`; and the binary expansion of $\mathrm{vrad}(d,c,|x|)$ is polynomial-time computable by `pt_bits_vrad`. Pair-encoding these components constructs exactly the input to the indicator. Composing this polynomial-time construction with the polynomial-time indicator proves the claim.

**Key facts.** `Complexity.Codec.initLang_mem`, `Complexity.TQBFHard.pt_indicator`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.TQBFHard.pt_vwid`, `Complexity.TQBFHard.pt_cpAt`, `Complexity.TQBFHard.pt_bits_vrad`, `Complexity.PolyTimeComputable.comp`.
