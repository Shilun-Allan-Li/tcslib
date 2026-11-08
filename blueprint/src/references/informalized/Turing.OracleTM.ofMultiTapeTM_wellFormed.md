<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.ofMultiTapeTM_wellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formedness of the Embedded Machine

**Claim.** The oracle machine formed by adjoining three fresh states to a deterministic machine is well formed: its query state and its positive- and negative-answer states are pairwise distinct.

**Proof.** The three designated states are the distinct elements $0$, $1$, and $2$ in the $	exttt{Fin 3}$ summand of the enlarged state set. Distinct natural numbers give distinct elements of this finite type, and elements in this summand are distinct from states in the original-state summand. Thus the query state differs from each answer state, and the two answer states differ from one another.
