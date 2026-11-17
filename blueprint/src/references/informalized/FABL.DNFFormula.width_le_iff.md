<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFFormula.width_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula Width Criterion

**Claim.** A DNF formula has width at most $w$ if and only if every term in it has width at most $w$.

**Proof.** If the formula width is at most $w$, then each term’s width is at most the formula width (`FABL.DNFFormula.width_le_of_mem`), hence at most $w$. Conversely, suppose every term has width at most $w$. The formula width is obtained by folding through the list of terms, taking the maximum of the current value and each term width, starting from zero. At each step both quantities in that maximum are at most $w$, so the maximum remains at most $w$; induction through the list gives formula width at most $w$ (`FABL.DNFFormula.foldl_max_le`). This also covers an empty list, whose initial width is zero.

**Key facts.** `FABL.DNFFormula.width_le_of_mem`, `FABL.DNFFormula.foldl_max_le`.
