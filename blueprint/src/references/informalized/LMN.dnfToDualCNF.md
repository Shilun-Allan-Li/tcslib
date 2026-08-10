<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: dnfToDualCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# De Morgan dual of a DNF

**Definition.** For `φ : DNF n`,

`dnfToDualCNF φ = φ.map (fun term => term.map Literal.flipNeg)`

— keep the list-of-lists shape but flip the polarity of every literal
(`Literal.flipNeg ⟨v, b⟩ = ⟨v, !b⟩`). Since `DNF n` and `CNF n` are both
`List (Term n)`, the same data is now read the other way round: each term
(a conjunction) becomes a clause (a disjunction). This is
`¬(⋁ᵢ ⋀ⱼ lᵢⱼ) = ⋀ᵢ ⋁ⱼ ¬lᵢⱼ`.

Two properties are proved alongside it:

- `dnfToDualCNF_width` — `(dnfToDualCNF φ).width = φ.width`: widths are clause
  lengths and `List.map` preserves length (`List.map_map`, `List.length_map`,
  `congr 1`).
- `dnfToDualCNF_eval` — `CNF.eval (dnfToDualCNF φ) x = !(DNF.eval φ x)`: an outer
  induction on the term list turning `List.any`/`List.all` into each other via
  `Bool.not_or`, and an inner induction on the literals of a single term using
  `Literal.flipNeg_eval` and `Bool.not_and`.

**Used in.** The AND-side compressions — `and_of_lit_children_cnf` and
`child_depth_le1_has_signed_dnf` — where a negated gate reference must be turned
from a width-`l` DNF into a width-`l` CNF. `cnfToDualDNF` (in
`BooleanAnalysis/Switching.lean`) is the opposite direction, used on the OR side.
