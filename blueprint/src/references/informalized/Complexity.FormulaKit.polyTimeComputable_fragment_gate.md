<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/FormulaKit/Emit.lean :: Complexity.FormulaKit.polyTimeComputable_fragment_gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Gate Encoding

**Claim.** If each wire index can be output in unary in polynomial time, then the binary fragment encoding of the CNF gate obtained by relabeling the truth-table clauses is polynomial-time computable.

**Proof.** Apply the polynomial-time relabeling result to the fixed formula `template ℓ p` and the wire map. Its hypothesis asks for unary polynomial-time computability of each wire index below the formula's number of variables. The template uses at most $\ell$ variables (`template_numVars_le`), so every such index is below $\ell$ and the assumed wire condition supplies exactly the required computation. The relabeling result then gives polynomial-time computability of the fragment encoding.

**Key facts.** `Complexity.FormulaKit.polyTimeComputable_fragment_relabel`, `Complexity.FormulaKit.template_numVars_le`.
