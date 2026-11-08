<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Equality Test

**Claim.** For polynomial-time computable $f,g\colon\{0,1\}^*\to\{0,1\}^*$, the function outputting $[1]$ if $f(y)=g(y)$ and $[0]$ otherwise is polynomial-time computable.

**Proof.** Pair-encode $f(y)$ and $g(y)$, which is possible in polynomial time. The proof computes two polynomial-time Boolean tests on this encoding. The first checks whether the two decoded components have equal lengths (`polyTimeComputable_lenEq`). The second XORs corresponding bits and keeps the true bits; it then tests whether the resulting string is empty. XOR is polynomial-time computable, and the transducer that outputs a true bit exactly when it reads a true bit is polynomial-time computable; emptiness is polynomial-time decidable (`polyTimeComputable_isNil`). The characterization `eq_iff_xor` says that the original strings are equal exactly when their lengths agree and every bit in their zipped XOR is false. The fact `keepTrue_eq_nil_iff` identifies the latter condition with emptiness of the retained-true string. Thus the conjunction of the two tests is precisely the equality indicator, and polynomial-time closure under conjunction gives the result.

**Key facts.** `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_lenEq`, `Complexity.polyTimeComputable_xorD`, `Complexity.polyTimeComputable_transduce`, `Complexity.polyTimeComputable_isNil`, `Complexity.polyTimeComputable_and`, `Complexity.TQBFHard.eq_iff_xor`, `Complexity.TQBFHard.keepTrue_eq_nil_iff`, `Complexity.xorD_pairEncode`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
