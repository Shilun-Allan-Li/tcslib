<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.card_tribeFrequencyPart_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of Block Frequencies

**Claim.** The sum of the counts of positions of $T$ in each block equals the cardinality of $T$.

**Proof.** For each block, map its counted positions to their corresponding positions in the full set of $sw$ coordinates. This map is injective, so it preserves the count. The images from distinct blocks are disjoint, since a coordinate belongs to only one block (`disjoint_tribeOffsetEmbed`). Their union is exactly $T$ (`tribeFrequencyPart_biUnion`). Thus the sum of the block counts is the cardinality of that disjoint union, namely $|T|.

**Key facts.** `FABL.disjoint_tribeOffsetEmbed`, `FABL.tribeFrequencyPart_biUnion`.
