<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean :: Complexity.LogProg.vword_unary₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Input with One Register

**Claim.** In unary-prefix mode, the virtual word built from the encoded pair $(1^n,w)$ and the single register $r$ is the encoded pair $(1^n,V(r))$.

**Proof.** The first segment is the initial run of ones in the input. By `takeWhile_pairEncode_replicate`, this is $1^{2n}$, and it is rendered plainly. The sole argument segment contains $V(r)$ and is also rendered plainly. The virtual-word construction joins these two rendered segments with the separator $(0,1)$, so the result is $1^{2n}$ followed by that separator and $V(r)$. By `dbl_replicate`, doubling $1^n$ gives $1^{2n}$; the identity `pairEncode_eq_dbl` then identifies this concatenation with the encoded pair $(1^n,V(r))$.

**Key facts.** `Complexity.LogProg.takeWhile_pairEncode_replicate`, `Complexity.LogProg.dbl_replicate`, `Turing.pairEncode_eq_dbl`.
