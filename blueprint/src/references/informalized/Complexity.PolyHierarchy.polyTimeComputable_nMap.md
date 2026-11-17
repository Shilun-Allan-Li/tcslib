<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Normalize.lean :: Complexity.PolyHierarchy.polyTimeComputable_nMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time tuple transformation

**Claim.** Under the stated polynomial-time hypotheses on $f$ and the unary length functions, the specified $i$-fold tuple transformation is polynomial-time computable for every $i\in\mathbb N$.

**Proof.** First build the base map on an encoded pair $p$: decode its two components, pad the second component of the decoded second input using the first component of the decoded first input, pair that result with the decoded first input, and apply $f$. The projections, pairing, padding, and composition results show that this base map is polynomial-time computable. Likewise, the decoder that takes the second component of the parameter and pads a supplied word is polynomial-time computable. The side word is polynomial-time computable by pairing the two unary words. The recursive tuple-decoding theorem now gives a polynomial-time map on a parameter and an input word. Feed it the side word formed from the $(i+1)$-fold first projection of $z$ and the original $z$; iteration, pairing, identity, and composition preserve polynomial-time computability. Unfolding the definitions identifies this composite with the stated transformation.

**Key facts.** `Complexity.PolyHierarchy.polyTimeComputable_padDecode`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_tupleDecode`, `Complexity.polyTimeComputable_iterate_pairFstD`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_id`.
