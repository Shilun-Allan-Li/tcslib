<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: razborovEncode_go_numFree_invariant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The encoder loop fixes exactly one free variable per path step

**Claim.** Let `f : DNF n` have, in every clause, `Nodup` literals with
variable-injective literals. Let `path`, `ρ₀`, `σ` satisfy: `ρ₀` and `σ` have the
same free variables (`∀ v, ρ₀ v = none ↔ σ v = none`), `IsCanonicalPath f ρ₀ path`
(i.e. `path` is a prefix of `(canonicalDTree f ρ₀).deepPath`),
`path.length ≤ (canonicalDTree f ρ₀).depth`, and `path.length < fuel`. Then
`(razborovEncode.go f w fuel path ρ₀ σ []).1.numFree + path.length = σ.numFree`.

**Proof.** `induction fuel generalizing path ρ₀ σ`.

1. `fuel = 0`: contradicts `path.length < fuel` (`Nat.not_lt_zero`).
2. `path = []`: the loop returns `σ` immediately — `simp [razborovEncode.go]`.
3. `path = step :: rest`, so `0 < (canonicalDTree f ρ₀).depth`. Unfold the loop
   and case on `f.find? (fun t => decide (¬Term.killedBy t ρ₀))`:
   - `none`: every clause is killed, so `canonicalDTree_depth_zero_of_killed`
     gives depth `0` — `omega`.
   - `some t_clause` with free-literal list
     `fli = t_clause.zipIdx.filter (fun p => decide (p.1.var ∈ ρ₀.freeVars))`:
     - `fli = []`: no literal of `t_clause` is free, and `¬Term.killedBy` forces
       each `ρ₀ l.var = some (!l.neg)`, i.e. `Term.fixedBy t_clause ρ₀`; then
       `canonicalDTree_depth_zero_of_fixed` contradicts the positive depth
       (`omega`).
     - `fli = fl :: fls`: set `pcl := processClauseLits (fl :: fls) path ρ₀ σ`
       and strip the accumulator with `encode_go_acc`, then combine:
       * `processClauseLits_numFree_σ` (with the free-literal and
         `processClauseLits_freeLits_pairwise_var` distinctness facts):
         `pcl.2.2.1.numFree + min lits.length path.length = σ.numFree`.
       * `processClauseLits_freeVars_agree`: the ρ/σ agreement carries to `pcl`.
       * `canonicalDTree_deepPath_match_freeLits` plus `hcanon` and
         `List.getElem_take` give the index-matching hypothesis
         `lits[k].1.var = path[k].1`.
       * `canonicalPath_preserve_processClauseLits` then yields both
         `IsCanonicalPath f pcl.2.1 pcl.1` and the new depth bound.
       * `processClauseLits_path_le` makes `fuel` suffice; the tight length
         identity `pcl.1.length + min lits.length path.length = path.length`
         is `processClauseLits_path_length_eq`.
       * Applying the induction hypothesis to the recursive call and `omega`
         finishes.

**Used in.** `razborovEncode_fst_numFree_eq` (private, same file), where it is
instantiated with `ρ₀ = σ = ρ` and `path.length = d` to conclude that the
encoder's γ-output is an `(s − d)`-restriction — the counting step of the
switching lemma.
