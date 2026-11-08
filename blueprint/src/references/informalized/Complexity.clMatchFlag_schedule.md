<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatchFlag_schedule -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scheduled Work-Head Position Equality

**Claim.** The comparison flag formed from the movement-count row at time $s$ and two copies of the movement-count word at time $t$ is true exactly when the work-head positions on tape $\tau$ at those times agree.

**Proof.** The two target words are identical, so their decoded numbers occur on opposite sides of the equality defining the comparison flag. Decoding the binary words recovers their original counts (`clNum_bits`), and the flag’s defining equality is therefore equivalent to equality of the signed differences between the positive- and negative-slot counts (`clSigned_eq`). The movement-count schedule identifies each such signed difference at time $s$ or $t$ with the work-head position on tape $\tau$ (`clCounts_schedule`). Substituting those two identities turns the comparison into equality of the head positions, as claimed.

**Key facts.** `Complexity.clNum_bits`, `Complexity.clSigned_eq`, `Complexity.clCounts_schedule`.
