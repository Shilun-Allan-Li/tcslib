<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: canonicalPath_preserve_processClauseLits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Processing one clause keeps the remaining path canonical

**Claim.** Let `f : DNF n`, `lits : List (Literal n × ℕ)`,
`path : List (Fin n × Bool)`, `ρ₀ σ : Restriction n`. Assume `IsCanonicalPath f ρ₀
path` (`path` is a prefix of `(canonicalDTree f ρ₀).deepPath`) with
`path.length ≤ (canonicalDTree f ρ₀).depth`; that the `k`-th literal variable of
`lits` matches the `k`-th path variable for all `k < min lits.length path.length`;
and that `t` is the first non-killed clause (`f.find? … = some t`), with literals
determined by their variables and duplicate-free, and
`lits = t.zipIdx.filter (·.1.var ∈ ρ₀.freeVars)`. Then, writing
`(path', ρ', _, _) = processClauseLits lits path ρ₀ σ`: `IsCanonicalPath f ρ' path'`
and `path'.length ≤ (canonicalDTree f ρ').depth`.

**Proof.** `private` helper (`set_option maxHeartbeats 1600000`); the step that
keeps the Razborov encoder's loop invariant alive.

1. `processClauseLits_fst_eq_drop` gives
   `path' = path.drop (min lits.length path.length)`.
2. **Case `path.length ≤ lits.length`.** The min is `path.length`, so
   `List.drop_length` makes `path' = []`; `IsCanonicalPath` holds by `simp` and the
   depth bound is `Nat.zero_le _`.
3. **Case `lits.length < path.length`.** Since
   `0 < path.length ≤ (canonicalDTree f ρ₀).depth`, the tree is not a leaf, so
   `canonicalDTree_depth_zero_of_killed` / `canonicalDTree_depth_zero_of_fixed`
   rule out "all terms killed" and "some term fixed", and
   `canonicalDTree_alive_eq_termSubTree'` rewrites the tree as `termSubTree t ρ₀ cont`.
4. After transferring `lits` to the plain filtered literal list
   (`zipIdx_filter_length`, `zipIdx_filter_getElem_fst`),
   `processClauseLits_termSubTree_drop` yields
   `(canonicalDTree f ρ₀).deepPath.drop lits.length = (cont ρ').deepPath`.
5. **Fuel decreases** (`ρ₀.numFree ≥ ρ'.numFree + 1`): `processClauseLits_numFree_ρ_eq`
   says `ρ'` loses exactly `lits.length` free variables, and `lits.length ≠ 0` —
   else `t` has no free literal, hence is `Term.fixedBy ρ₀` (it is not `killedBy`,
   by `List.find?_some`), contradicting step 3. So `cont_eq_canonicalDTree`
   identifies `cont ρ'` with `canonicalDTree f ρ'`.
6. `List.drop_take` rewrites `path.drop lits.length` as a `take` of
   `deepPath.drop lits.length`; with steps 4–5 this exhibits `path'` as a `take` of
   `(canonicalDTree f ρ').deepPath`, which is `IsCanonicalPath` by definition, and
   `DecisionTree.length_deepPath` gives the depth bound.

**Used in.** `razborovEncode_go_numFree_invariant`, right after
`canonicalDTree_deepPath_match_freeLits` supplies the variable-matching hypothesis.
