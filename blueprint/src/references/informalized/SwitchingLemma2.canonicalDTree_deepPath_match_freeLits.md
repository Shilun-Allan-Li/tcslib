<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: canonicalDTree_deepPath_match_freeLits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The deep path queries the first alive clause's free literals in order

**Claim.** Let `f : DNF n`, `ρ : Restriction n`, and suppose
`f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t`, with the literals of `t`
determined by their variables (`hnd`) and duplicate-free (`hnodup`). Let
`flis = t.zipIdx.filter (fun p => p.1.var ∈ ρ.freeVars)` be the indexed free
literals of `t`. Then for every `k` in range of both lists, the `k`-th step of
`(canonicalDTree f ρ).deepPath` queries the variable of the `k`-th entry of
`flis`: `((canonicalDTree f ρ).deepPath[k]).1 = (flis[k]).1.var`.

**Proof.** `private` helper; reduces the canonical tree to a `termSubTree` and
applies the corresponding `termSubTree` fact.

1. **`ρ` leaves `f` alive** (`halive`): if all terms were `killedBy ρ`, or some
   term were `fixedBy ρ`, then `canonicalDTree f ρ` would be a leaf
   (`canonicalDTree_depth_zero_of_fixed`), hence have empty `deepPath`,
   contradicting `hk_path : k < deepPath.length`. Both branches are obtained by
   `contrapose!` on `hk_path`.
2. **Variables of `t` are pairwise distinct** (`h_pairwise`): from `hnodup` via
   `List.Pairwise.imp_of_mem`, using `hnd` to convert `var`-equality into literal
   equality.
3. `canonicalDTree_alive_eq_termSubTree'` rewrites `canonicalDTree f ρ` as
   `termSubTree t ρ cont` with the continuation
   `fun ρ' => if Term.fixedBy t ρ' then .leaf true else canonicalDTree.go f ρ.numFree ρ'`.
4. `termSubTree_deepPath_var_match` gives exactly the wanted indexing statement,
   but phrased with `t.filter (·.var ∈ ρ.freeVars)` instead of the `zipIdx`
   version; `zipIdx_filter_length` and `zipIdx_filter_getElem_fst` transport the
   length side-goal and the element itself across `zipIdx`.

**Used in.** `razborovEncode_go_numFree_invariant` (as the `hmatch_pcl` hypothesis
fed to `canonicalPath_preserve_processClauseLits`): it certifies that the encoder
consumes path steps in the same order as the clause's free literals.
