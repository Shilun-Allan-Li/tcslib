# layer (U7) duplication searches

| # | Query | Tool | Result |
|---|---|---|---|
| 1 | `foldr max` (all lemmas) | grep Mathlib/ + TCSlib/ | Mathlib `List.max_le_of_forall_le`, `List.le_max_of_le`, `List.foldr_max_of_ne_nil` (Mathlib/Data/List/MinMax.lean) — NOT in the module's import closure (`Unknown constant`, log NL-006); TCSlib: private `foldr_max_le` (ClassPSPACE/TQBFHardTseitin.lean:99), private `le_foldr_max` (LogspaceUniformCanon.lean:51), private `taut_le_max` (ClassNP/Tautology.lean:965) — inequalities, private; public `DAGGate.getD_lt_depth` (DAGCircuit.lean:592) used |
| 2 | `(∀ y ∈ l, y = k) → y₀ ∈ l → l.foldr max 0 = k` | `exact?` probe DupNL (log DupNL-001) | no lemma found → private `foldr_max_eq_of_forall` |
| 3 | `(∀ y ∈ l, y ≤ k) → l.foldr max 0 ≤ k` | `exact?` probe DupNL | no lemma in closure (not needed in the end) |
| 4 | `foldr max 0 =` | grep TCSlib | only SAT.lean:1730 (append, private context) and DAGFanin rfl lines; no equality-for-constant-list fact |
| 5 | getD lemmas | grep toolchain src + Mathlib/Data/List/GetD.lean | used `List.getD_eq_getElem?_getD`, `List.getD_cons_zero/succ`, `List.getD_append`, `List.getD_append_right`, `List.getD_eq_getElem` |
| 6 | prefix lemmas | grep toolchain Init/Data/List/Sublist.lean | used `List.prefix_append`, `List.prefix_refl`, `List.IsPrefix.trans/length_le/getElem/subset`, `List.getElem_concat_length` |
| 7 | range/fold | toolchain | used `List.range_succ`, `List.foldl_append`, `List.foldl_cons`, `List.foldl_nil` |
| 8 | GatesAcyclic facts | DAGCircuit.lean | used `GatesAcyclic.nil`, `GatesAcyclic.snoc`, `gatesAcyclic_iff` |
| 9 | DAG readers | DAGCircuit.lean / NANDForm.lean | used `depthAt_gate`, `DAGGate.depth_eq`, `depthAt_eq`, `depthAt_input`, `values_getD_gate`, `values_getD_input`, `DAGGate.getD_lt_depth`, `all_congr_mem`, `depth_eq`, `eval_eq`, `size_eq`, `isNANDForm_iff`, `DAGGate.isNAND_iff`, `DAGGate.eval_of_isNAND` (N1, frozen) |
| 10 | chain / layerAt / layerColumn facts | grep TCSlib for layerChain, layerAt | own definitions only (this file); no existing lemma |
| 11 | helper full names (17) | grep -rlw TCSlib audits | 0 hits outside this file |
