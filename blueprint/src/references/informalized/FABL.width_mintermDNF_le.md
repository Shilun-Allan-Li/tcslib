<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.width_mintermDNF_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width Bound for Minterm DNF

**Claim.** For every Boolean function on the $n$-dimensional sign cube, the width of its minterm disjunctive normal form is at most $n$.

**Proof.** A DNF has width at most $n$ exactly when every term in it has width at most $n$ (DNFFormula.width_le_iff). Each term of the minterm DNF is the minterm associated with some cube point, by the definition of that DNF. Every such minterm has width exactly $n$ (DNFTerm.width_minterm), and hence at most $n$.

**Key facts.** `FABL.DNFFormula.width_le_iff`, `FABL.DNFTerm.width_minterm`.
