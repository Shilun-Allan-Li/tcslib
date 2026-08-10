<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: Literal.flipNeg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Flipping the polarity of a literal

**Definition.** For `l : Literal n` (a structure with fields `var : Fin n` and
`neg : Bool`), `Literal.flipNeg l := ⟨l.var, !l.neg⟩` — the same variable with the
opposite polarity. This is the atomic step of De Morgan duality; the dual of a CNF
is obtained by mapping it over every literal (`cnfToDualDNF`).

Three small facts are proved alongside it:

- `Literal.flipNeg_eval` : `l.flipNeg.eval x = !(l.eval x)`, by unfolding
  `Literal.eval` and `cases l.neg <;> simp`;
- `Literal.flipNeg_var` : `l.flipNeg.var = l.var`, by `rfl`;
- `Literal.flipNeg_injective` : `Function.Injective Literal.flipNeg`, from
  `Literal.mk.injEq` after `cases` on both literals.

**Used in.** `cnfToDualDNF` and its properties — `cnfToDualDNF_eval`,
`cnfToDualDNF_width`, `cnfToDualDNF_nodup` and `cnfToDualDNF_inj` — which together
transfer the DNF switching lemma to CNFs.
