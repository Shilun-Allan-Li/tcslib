<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Normalize.lean :: Complexity.PolyHierarchy.altQuant_transfer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transfer of alternating quantifiers

**Claim.** Under the stated length and surjectivity conditions on the decoder, and the compatibility of the maps $F_n$ with pair extension, the depth-$k$ alternating-quantifier condition over length-$B$ blocks for $V'$ is equivalent to the corresponding condition over length-$m$ blocks for $V$ on the transformed input.

**Proof.** Proceed by induction on the depth $k$, proving the equivalence for every starting quantifier type, index $n$, and word $w$. At depth zero, the hypothesis applied to $z=w$ applies because zero extensions leave the word unchanged; it identifies membership of $w$ in $V'$ with membership of $F_n(w)$ in $V$.

For the inductive step, express each depth-$(k+1)$ condition as its first quantifier applied to the depth-$k$ condition on the pair-extended word; this is the successor characterization of alternating quantifiers (`Complexity.altQuant_succ`). The first quantifiers transfer between block lengths $B$ and $m$ by the quantifier-transfer lemma (`Complexity.PolyHierarchy.qStep_transfer`): every length-$B$ block decodes to a length-$m$ block, and every length-$m$ block has a length-$B$ preimage. For each chosen block $v$ of length $B$, compatibility of $F$ with pair encoding identifies the transformed extended input with the pair extension of $F_n(w)$ by the decoded block. Apply the induction hypothesis at depth $k$, with the opposite quantifier type and index $n+1$, to this extended word. Its terminal membership premise follows from the original hypothesis, since this word is a one-step extension followed by the given $k$ further extensions; the indices agree because $n+(k+1)=(n+1)+k$. This establishes the equivalence at depth $k+1}.

**Key facts.** `Complexity.altQuant_succ`, `Complexity.PolyHierarchy.qStep_transfer`.
