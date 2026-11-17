<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFFormula.width_truncateWidth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width After Truncation

**Claim.** Deleting from a DNF formula every term whose width exceeds $w$ leaves a formula of width at most $w$.

**Proof.** By the formula width criterion (`FABL.DNFFormula.width_le_iff`), it suffices to check that every term in the filtered list has width at most $w$. Membership in the filtered list means the term passed the filter condition, namely that its width is at most $w$.

**Key facts.** `FABL.DNFFormula.width_le_iff`.
