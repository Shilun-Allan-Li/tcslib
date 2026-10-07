<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: list_all_eq_false_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# One failing member makes a list-wide `all` false

**Claim.** For `l : List α`, `p : α → Bool` and `a : α` with `a ∈ l` and
`p a = false`, we have `l.all p = false`.

**Proof.** Induction on `l` (`induction l with`).

1. `nil`: `a ∈ []` is impossible (`simp at ha`).
2. `cons hd tl`: `rw [List.all_cons]` turns the goal into
   `p hd && tl.all p = false`, then `by_cases heq : a = hd`.
   - If `a = hd`: `subst heq; simp [hp]` — the left conjunct is `false`.
   - Otherwise `a ∈ tl` (from `List.mem_cons.mp ha`, discarding the `a = hd`
     branch with `absurd rfl heq`), and `simp [ih hmem]` makes the right
     conjunct `false`.

**Remark.** The `Bool` counterpart of "a conjunction over a list fails if one
conjunct fails"; kept local rather than sourced from Mathlib.

**Used in.** `killedAll_implies_dtDepth_zero` (same file), where a killed
literal inside a term forces `Term.eval = false` via
`Literal.killedBy_eval_false`; also at `Switching/CanonicalDTree.lean:283` for
the same step.
