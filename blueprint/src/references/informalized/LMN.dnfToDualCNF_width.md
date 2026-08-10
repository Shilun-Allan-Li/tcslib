<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: dnfToDualCNF_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# De Morgan dualisation preserves width

**Claim.** For every `φ : DNF n`, the dual CNF `dnfToDualCNF φ` has the same width
as `φ`: `(dnfToDualCNF φ).width = φ.width`.

**Proof.** Both widths are `foldr max 0` over the list of term lengths, and
`dnfToDualCNF φ = φ.map (·.map Literal.flipNeg)` only rewrites literals, never
adds or removes them.

1. Unfold both sides with `simp only [dnfToDualCNF, CNF.width, DNF.width, Term.width]`.
2. `List.map_map` and `Function.comp_def` fuse the two nested `map`s, and
   `List.length_map` collapses `(t.map Literal.flipNeg).length` to `t.length`.
3. The two `foldr max 0` calls now differ only up to the fused function, closed by
   `congr 1`.

**Used in.** `and_of_lit_children_cnf`, where a gate's width-`l` DNF is dualised into
a width-`l` CNF and the width bound must be transported across the conversion.
