<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satReq_fields_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Request Projections

**Claim.** The fresh field, consumed field, phase field, unread input, polarity suffix, and current literal functions on Boolean words are polynomial-time computable.

**Proof.** The first three projections are obtained by composing the polynomial-time first and second projections of the paired-stream encoding: the fresh field uses the first projection twice, the consumed field uses the first projection after the second, and the phase field uses the second projection twice after the first. For the unread input, pair the consumed-field projection with the stream’s second projection and apply the polynomial-time operation that drops a prefix whose length is given by the first component. To obtain the polarity suffix, first apply the linear-time unary-token splitter to this unread input, encoded as a pair of its token and remainder; then take the second projection. The token-and-remainder encoding is polynomial-time by pairing polynomial-time functions, and the splitter itself has a linear-time machine. For the current literal, take the first projection of that same encoded split to recover the token, and append the first bit of the already computed polarity suffix. Both the projection and taking one bit are polynomial-time, and polynomial-time functions are closed under composition and pointwise concatenation. The pair-encoding identities justify each identification of these composed projections with the stated request fields.

**Key facts.** `Complexity.sat_pt_fields`, `Complexity.PolyTimeComputable.comp`, `Complexity.sat_pt_drop`, `Complexity.sat_pt_pair`, `Complexity.sat_pt_linear`, `Turing.FinTM.computesFunInTime_unaryToken`, `Turing.pairDecode_pairEncode`, `Complexity.sat_pt_head`, `Complexity.sat_pt_append`.
