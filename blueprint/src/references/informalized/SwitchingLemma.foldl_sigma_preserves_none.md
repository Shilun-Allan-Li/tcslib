<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: foldl_sigma_preserves_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The decoder's σ-fold preserves freeness

**Claim.** Let `t : Term n`, `entries : List (ℕ × Bool)`, `σ : Restriction n` and
`v : Fin n` with `σ v = none`. Then

```
entries.foldl (fun σ e => match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ v = none
```

Unlike `foldl_sigma_stable` there is no hypothesis about which variables the
entries target: every update writes `none`, so `v` stays free either way.

**Proof.** Induction on `entries`, generalizing `σ`.

1. `[]`: `simpa` from `hv`.
2. `e :: es`: `simp only [List.foldl_cons]` and `apply ih`, leaving the goal that
   the once-updated σ is still `none` at `v`. `match h : t.drop e.1` with:
   - `[]`: the step is a no-op, `simp [hv]`.
   - `l :: _`: `simp only [Function.update_apply]` and `split` — if `l.var = v`
     the new value is literally `none` (`exact rfl`), otherwise `exact hv`.

**Used in.** `processClauseLits_foldl_sigma_none`, in the branch where the clause
pass fixes `v` and the decoder's σ-fold must therefore report `v` as free.
