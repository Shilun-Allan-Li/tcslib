<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.card_e3LinConstraintsToE3Sat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the converted constraint multiset

**Claim.** Converting each constraint in a multiset of three-variable linear constraints over $\mathbb{F}_2$ into its four E3-SAT clauses produces a multiset of cardinality four times the original cardinality.

**Proof.** Induct on the multiset of constraints. The empty multiset produces no clauses, so both cardinalities are zero. For the inductive step, write the multiset as one constraint together with a remaining multiset. The conversion binds each original element to its clause multiset, so the resulting cardinality is the sum of the clause count for the chosen constraint and the cardinality for the remainder. The chosen constraint contributes four clauses by the clause-count result. By induction, the remainder contributes four times its cardinality. Adding these gives four times the cardinality of the original multiset.
