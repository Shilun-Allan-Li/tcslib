<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: canonicalDTree_alive_eq_termSubTree' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The same unfolding for `canonicalDTree` itself

**Claim.** Under the same three hypotheses as the unprimed version — `ρ` kills
not all terms of `f` (`h1`), fixes none of them (`h2`), and `t` is the first
non-killed term (`hfind : f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t`) —

```
canonicalDTree f ρ
  = termSubTree t ρ (fun ρ' => if decide (Term.fixedBy t ρ') then .leaf true
                               else canonicalDTree.go f ρ.numFree ρ')
```

Note the residual fuel in the continuation is `ρ.numFree`, one less than the
`ρ.numFree + 1` that `canonicalDTree` starts with.

**Proof.** A one-step wrapper.

1. `show canonicalDTree.go f (ρ.numFree + 1) ρ = _` — this is the definition of
   `canonicalDTree f ρ`, so the goal is now in `canonicalDTree.go` form.
2. `exact canonicalDTree_alive_eq_termSubTree f ρ ρ.numFree h1 h2 t hfind`. ∎

**Used in.** `TCSlib/BooleanAnalysis/Switching.lean` (lines ~1060 and ~1207),
where the canonical decision tree of an alive restriction has to be traced
literal-by-literal through the first alive term.
