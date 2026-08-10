<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: canonicalDTree_alive_eq_termSubTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The alive branch of `canonicalDTree.go` unfolds to `termSubTree`

**Claim.** Let `f : DNF n`, `ρ : Restriction n`, `fuel : ℕ`. Suppose not every
term of `f` is killed by `ρ` (`h1 : ¬ ∀ t ∈ f, Term.killedBy t ρ`), no term is
fixed by `ρ` (`h2 : ¬ ∃ t ∈ f, Term.fixedBy t ρ`), and the first non-killed term
is `t`, i.e. `f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t`. Then

```
canonicalDTree.go f (fuel + 1) ρ
  = termSubTree t ρ (fun ρ' => if decide (Term.fixedBy t ρ') then .leaf true
                               else canonicalDTree.go f fuel ρ')
```

**Proof.** Purely an unfolding of the three guards in the `fuel + 1` branch of
`canonicalDTree.go`.

1. `simp only [canonicalDTree.go]` exposes the two nested `dite`s and the
   `match` on `f.find? …`.
2. `rw [dif_neg h1, dif_neg h2]` discharges the "all killed → `leaf false`" and
   "some fixed → `leaf true`" branches, leaving the `find?` match.
3. `rw [hfind]` selects the `some t` arm, which is literally the right-hand
   side. ∎

Nothing mathematical happens here; the lemma exists so that later proofs can
step into the alive branch without re-deriving the guard elimination, and so
that `termSubTree`'s own lemmas (`termSubTree_deepPath_split`,
`termSubTree_cons_nonfree`, …) become applicable.

**Used in.** `canonicalDTree_alive_eq_termSubTree'` (same statement for
`canonicalDTree` itself, at `fuel = ρ.numFree`).
