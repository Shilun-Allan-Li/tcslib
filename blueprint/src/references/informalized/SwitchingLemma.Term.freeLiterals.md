<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Encoding.lean :: Term.freeLiterals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The free literals of a term under a restriction

**Definition.** For a term `t : Term n` (a list of `Literal n`) and a
restriction `ρ : Restriction n = Fin n → Option Bool`,

```
Term.freeLiterals t ρ = t.filter (fun l => decide (l.var ∈ ρ.freeVars))
```

is the sublist of literals of `t` whose variable is still unfixed by `ρ`, in the
original clause order. `Restriction.freeVars ρ` is
`Finset.univ.filter (fun i => (ρ i).isNone)`, the set of coordinates on which `ρ`
is `none`. The definition is `noncomputable` only because the file is under
`open Classical`, which supplies the membership decidability instance.

**Remark.** This is the term-level counterpart of the "surviving literals" notion
in the Razborov encoding: the literals a restricted clause still depends on, and
hence the ones the encoder would pair against decision-tree path entries.
`processClauseLits` in the same file consumes a list of
`Literal n × ℕ` (literal together with its position in the clause) rather than
this list, so `Term.freeLiterals` is currently unused elsewhere in `TCSlib` —
treat it as a helper the encoding chain does not yet route through.
