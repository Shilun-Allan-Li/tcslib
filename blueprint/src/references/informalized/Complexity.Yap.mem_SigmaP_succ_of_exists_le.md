<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.mem_SigmaP_succ_of_exists_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One More Existential Alternation

**Claim.** If $L'\in\Pi_i^{\mathsf P}$, and membership in $L$ is characterized by a polynomially bounded witness whose pairing with the input lies in $L'$, then $L\in\Sigma_{i+1}^{\mathsf P}$.

**Proof.** Use the polynomial-time map $g(z)=\langle\operatorname{fst}(z),\operatorname{dropMarker}(\operatorname{snd}(z))\rangle$. Pair decoding and re-encoding are polynomial-time, and dropping the marker is polynomial-time as well (`Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.KarpLipton.polyTimeComputable_dropMarker`, `Complexity.PolyTimeComputable.comp`, and `Complexity.PolyTimeComputable.pairEncode`). Thus the preimage $g^{-1}(L')$ remains in $\Pi_i^{\mathsf P}$ (`Complexity.preimage_mem_PiP`). The characterization of $\Sigma_{i+1}^{\mathsf P}$ asks for an existential witness of one exact polynomially specified length, so choose length $(B+1)(|x|+1)^b$ and use this preimage as the inner language (`Complexity.mem_SigmaP_succ_iff`).

For $x\in L$, take the assumed witness $u$, of length at most $B(|x|+1)^b$. Pad it by a marker: put $k=(B+1)(|x|+1)^b-|u|-1$, and let $U$ consist of $k$ true bits, then a false bit, then $u$. Since $(|x|+1)^b\ge1$, this is a nonnegative padding length and $|U|=(B+1)(|x|+1)^b$. On the paired input $\langle x,U\rangle$, the map $g$ recovers $\langle x,u\rangle$: the marker-removal identity says that dropping the marker from the padded string returns $u$ (`Complexity.KarpLipton.dropMarker_marker`). Hence $g(\langle x,U\rangle)\in L'$. Conversely, if some witness $U$ of the required length maps into $L'$, its first decoded component is $x$; the assumed implication from membership of $\langle x,u\rangle$ in $L'$ to $x\in L$ yields $x\in L$. These two directions establish the exact-witness characterization.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.KarpLipton.polyTimeComputable_dropMarker`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.preimage_mem_PiP`, `Complexity.mem_SigmaP_succ_iff`, `Complexity.KarpLipton.dropMarker_marker`.
