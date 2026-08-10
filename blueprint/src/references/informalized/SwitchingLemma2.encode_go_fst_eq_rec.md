<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: encode_go_fst_eq_rec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# One encoder step does not change γ

**Claim.** Suppose the encoder's first non-killed clause under `ρ₀` is `t_clause`
and its free-literal list is nonempty, `(t_clause.zipIdx).filter (·.1.var ∈ ρ₀.freeVars)
= fl :: fls`. Put `pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ`. Then

`(razborovEncode.go f w (fuel+1) (step :: rest) ρ₀ σ []).1
  = (razborovEncode.go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 []).1`,

i.e. the returned restriction `γ` of a `fuel+1` run agrees with that of the
recursive run on the processed state.

**Proof.** Two steps.

1. `cases'` on `f.find? (fun t => ¬t.killedBy ρ₀)` and `simp_all [razborovEncode.go]`
   unfold one loop iteration; the `none` arm is impossible given `hfind`, and the
   `some` arm rewrites the left side to the recursive call carried out with the
   accumulator `pcl.2.2.2 ++ [(w, false)]` instead of `[]`.
2. `encode_go_fst_acc` — the first component is independent of the accumulator —
   closes the goal.

**Note.** Purely a plumbing lemma: the aux accumulator grows, `γ` does not.
