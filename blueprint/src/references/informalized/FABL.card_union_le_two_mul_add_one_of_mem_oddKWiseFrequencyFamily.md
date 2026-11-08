<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.card_union_le_two_mul_add_one_of_mem_oddKWiseFrequencyFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Union Size in a Frequency Family

**Claim.** If $S$ and $T$ belong to the family of sets of size at most $m$ together with sets of size $m+1$ containing $i$, then $|S\cup T|\le 2m+1$.

**Proof.** There are four membership cases. If both sets have size at most $m$, the low-degree union bound gives $|S\cup T|\le 2m$ (`card_union_le_two_mul_of_mem_lowDegreeFourierFamily`). If one has size at most $m$ and the other is in the extension, their sizes are at most $m$ and exactly $m+1$, respectively, so the general bound $|S\cup T|\le |S|+|T|$ gives at most $2m+1$. This applies whichever set is in the extension. Finally, if both are in the extension, each has size $m+1$ and contains $i$ (`mem_oddKWiseFrequencyExtension_card`), so their intersection has at least one element. The identity $|S\cup T|+|S\cap T|=|S|+|T|$ then yields $|S\cup T|\le 2(m+1)-1=2m+1$.

**Key facts.** `FABL.card_union_le_two_mul_of_mem_lowDegreeFourierFamily`, `FABL.mem_oddKWiseFrequencyExtension_card`.
