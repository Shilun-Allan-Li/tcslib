<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: CNF.dual_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable distinctness under dualization

**Claim.** If no clause of a CNF contains two distinct literals with the same variable, then no term in its De Morgan dual DNF contains two distinct literals with the same variable.

**Proof.** Take a term in the dual DNF. By the definition of dualization, it is the list obtained by flipping the literals in some clause of the original CNF. Any two literals in this term therefore come from two literals in that clause. Flipping a literal preserves its variable (`Literal.flipNeg_var`), so if the two resulting variables agree, the original variables agreed as well. The hypothesis on the clause then says the original literals were equal. Flipping both preserves equality, so the two literals in the dual term are equal, as desired.

**Key facts.** `Literal.flipNeg_var`.
