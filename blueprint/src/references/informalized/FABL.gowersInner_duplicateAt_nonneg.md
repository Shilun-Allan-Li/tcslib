<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersInner_duplicateAt_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity After Duplication

**Claim.** The Gowers inner product of a family after replacing a coordinate by a fixed bit is nonnegative.

**Proof.** By the duplicate-coordinate inner product formula (FABL.gowersInner_duplicateAt), this inner product is the average over $y$ of the square of a real half expectation. Each such square is nonnegative, so its average is nonnegative as well.

**Key facts.** `FABL.gowersInner_duplicateAt`.
