<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNF.lean :: Complexity.exists_cnf_boolFun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# CNF Representation of Boolean Functions

**Claim.** Every Boolean function on $\{0,1\}^{\ell}$ is computed by a CNF with at most $2^\ell$ clauses, at most $\ell$ variables, and clause width at most $\ell$.

**Proof.** Use the falsifying CNF of $f$, formed so that each input on which $f$ is false contributes a clause excluding that input. The four properties of this construction are supplied directly by `falsifyingCNF_numVars`, `falsifyingCNF_length`, `falsifyingCNF_width`, and `falsifyingCNF_eval`: it uses at most the $$-coordinate variables, has at most $2^\ell$ clauses, each clause has width at most $\ell$, and its evaluation at any assignment is $f$ on the first $$ coordinates. Here each occurrence of the malformed glyph is intended to be the parameter $\ell$.

**Key facts.** `Complexity.falsifyingCNF_numVars`, `Complexity.falsifyingCNF_length`, `Complexity.falsifyingCNF_width`, `Complexity.falsifyingCNF_eval`.

**Caveat.** The informal statement says DNF, but the formal theorem constructs a CNF. The proof source gives only the CNF construction; it does not establish the requested DNF assertion.
