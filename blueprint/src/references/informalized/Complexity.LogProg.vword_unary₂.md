<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean :: Complexity.LogProg.vword_unary₂ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Input with Two Registers

**Claim.** In unary-prefix mode, the virtual word built from the encoded pair $(1^n,w)$ and registers $r,s$ is the encoded pair whose first component is $1^n$ and whose second component is the encoded pair $(V(r),V(s))$.

**Proof.** The first segment is the initial run of ones in the input, which is $1^{2n}$ by `takeWhile_pairEncode_replicate`; it is rendered plainly. The two argument segments contain $V(r)$ and $V(s)$, and both are rendered doubled because there are two arguments. By the definition of the virtual word, separators are inserted between these consecutive rendered segments. Thus the result is $1^{2n}$, then a separator, then the doubled $V(r)$, another separator, and the doubled $V(s)$. The identity `pairEncode_eq_dbl` packages the last three pieces as the encoding of $(V(r),V(s))$. The identity `dbl_replicate` rewrites the prefix $1^{2n}$ as the doubled unary word, and `pairEncode_eq_dbl` packages the whole expression as the encoding with first component $1^n$.

**Key facts.** `Complexity.LogProg.takeWhile_pairEncode_replicate`, `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`.
