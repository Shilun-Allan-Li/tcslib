<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean :: Complexity.LogProg.pairWords_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Encoded Pair

**Claim.** For every $n$ and Boolean words $u,w$, removing the leading run of ones and the following two bits from the encoding of $(1^n,\operatorname{pairEncode}(u,w))$ leaves the encoding of $(u,w)$; decoding that remainder returns $(u,w)$.

**Proof.** The leading run of ones in the outer encoding has length $2n$ (`tRun_pairEncode`); the doubled unary word is a run of exactly that many ones (`dbl_replicate`). The outer encoding can be written as the doubled first component, the separator $01$, and the second component (`pairEncode_eq_dbl`). Thus dropping the leading run and the next two separator bits leaves precisely $\operatorname{pairEncode}(u,w)$. The pair-decoding identity (`Turing.pairDecode_pairEncode`) then returns $(u,w)$, and the default value in the definition of `pairWords` is not needed.

**Key facts.** `Complexity.LogProg.tRun_pairEncode`, `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`, `Turing.pairDecode_pairEncode`.
