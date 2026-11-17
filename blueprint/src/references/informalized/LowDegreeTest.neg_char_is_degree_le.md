<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.neg_char_is_degree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negated characters have bounded degree

**Claim.** For every subset $S$ and every integer $d\ge 1$, the negated Walsh character $-\chi_S$ has degree at most $d$.

**Proof.** First, the negated Walsh character has degree at most one (`LowDegreeTest.neg_char_is_degree_le_one`). If $d=1$, this gives the result directly. For each subsequent degree bound, use the fact that degree at most $d$ implies degree at most $d+1$ (`LowDegreeTest.degree_le_succ`). Induction therefore extends the degree-one bound to every $d\ge1$.

**Key facts.** `LowDegreeTest.neg_char_is_degree_le_one`, `LowDegreeTest.degree_le_succ`.
