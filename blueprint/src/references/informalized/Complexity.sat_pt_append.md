<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Polynomial-Time Functions

**Claim.** If $f$ and $g$ are polynomial-time computable functions from binary strings to binary strings, then $x\mapsto f(x)++g(x)$ is polynomial-time computable.

**Proof.** First compute the pair encoding of $f(x)$ and $g(x)$; this is polynomial-time by the closure of polynomial-time computable functions under composition and the pairing construction for two such functions. Then apply the linear-time pair-decoding-and-concatenation procedure to this encoding. Pair encoding followed by decoding recovers exactly $(f(x),g(x))$, so the final output is $f(x)++g(x)$. Composition with the linear-time procedure preserves polynomial time.

**Key facts.** `Complexity.sat_pt_pair`, `Complexity.PolyTimeComputable.comp`, `Complexity.sat_pt_linear`, `Turing.FinTM.computesFunInTime_pairConcat`, `Turing.pairDecode_pairEncode`.
