<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.polyTimeComputable_padDecode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time padding decoder

**Claim.** The function sending $z$ to $\operatorname{pad}(\pi_1(z),\pi_2(z))$ is polynomial-time computable.

**Proof.** Define an auxiliary map that decodes $z$ as a pair $(a,v)$ and, when $v$ has a last true bit with prefix $u$, returns the encoding of $(a,u)$; if either decoding or splitting fails, it returns the empty word. The linear-time machine for checking pair validity and the polynomial-time machine for this strip-last operation yield a polynomial-time auxiliary map. Its validity test, composed with the auxiliary map, lets us distinguish valid pair encodings from invalid ones. For valid pairs, compose the auxiliary map with a length-equality test on its decoded components: if the lengths agree, take the second decoded component; otherwise take the first. For invalid pairs, take the first total projection, which is the empty word in this case. Polynomial-time closure under composition and conditional choice shows that this whole construction is polynomial-time computable. Finally, when the pair is valid, decoding the auxiliary map's re-encoding recovers $(a,u)$; thus the length test and chosen component implement the padding rule. When splitting fails, the auxiliary output is empty and the same conditional construction returns $a$. Invalid inputs also produce the stipulated default from the total projections. Hence the constructed function is precisely the padding decoder on every input.

**Key facts.** `Turing.FinTM.computesFunInTime_stripLast`, `Complexity.polyTimeComputable_of_linear`, `Turing.FinTM.computesFunInTime_pairValid`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_lenEq`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_pairFstD`, `Turing.pairDecode_pairEncode`.
