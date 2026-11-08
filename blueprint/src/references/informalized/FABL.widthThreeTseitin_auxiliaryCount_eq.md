<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.widthThreeTseitin_auxiliaryCount_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Auxiliary Variable Count

**Claim.** For a finite CNF formula with $s$ clauses and any natural-number width parameter $w$, the auxiliary-variable count is $(w-3)s$.

**Proof.** By definition, the auxiliary-variable count is $(w-3)$ times the formula's size, and the size is its number of clauses. Unfolding that definition gives the stated equality.
