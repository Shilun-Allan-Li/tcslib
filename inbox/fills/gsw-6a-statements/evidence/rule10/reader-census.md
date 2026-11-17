# Reader census (check 6): every foreign definition that a 6a target's sketch or a definition's body reads

Line numbers are at the issue base `f6f295a6` for existing files. For the new files, they are at the statement head.

The rows cover:
- the sub-agents' censuses (`subagents/bp/REPORT.md` §5, `subagents/fa/REPORT.md` §5);
- the lead's census for `NANDForm.lean`, `NANDLayering.lean` and O1's `Combinators.lean`.

"Notation" marks reducible abbreviations and projection coercions, which are never sealed.

## Present readers

| Foreign definition (file:line) | Read by | Reader(s) (file:line) |
|---|---|---|
| `TreeCircuit.eval` (Basic:144) | BarringtonConverse, Barrington (C13, C16), Combinators F1–F3, CarrySave, Compare, ModSum; O1's moved proofs | `TreeCircuit.eval_lit` Basic:150; `eval_node_true_iff`/`_false_iff` Basic:155/163; `TreeCircuit.eval_node_true`/`_false` TreeDAG:126/132 |
| `TreeCircuit.depth` (Basic:176), node case | C14, C17–C21, F1–F10 | `TreeCircuit.depth_node` Basic:213; `maxDepth_nil`/`_cons` Basic:228/231; `depth_le_maxDepth` Basic:249 |
| `TreeCircuit.maxFanin` (Basic:194), node case | C13–C15, C17–C21, F1–F10 | `TreeCircuit.maxFanin_node` Basic:223; `maxFaninL_nil`/`_cons` Basic:242/245; `maxFanin_le_maxFaninL` Basic:257 |
| `TreeCircuit.size` (Basic:181), node case | C24 sketch; O1 `size_balanced_le` | `TreeCircuit.size_node` Basic:218; `sumSize_nil`/`_cons` Basic:235/238; `size_succ_le_two_pow` Basic:313 |
| `TreeCircuit.sumSize`, `maxFaninL`, `maxDepth` (Basic) | O1's moved proofs, F-rows | `sumSize_nil`/`_cons`, `maxFaninL_nil`/`_cons`, `maxDepth_nil`/`_cons` (all `rfl`, Basic) |
| `TreeCircuit.balanced` (Combinators, new owner) | BarringtonConverse (`wireComp`, `toFormula`), Compare, ModSum | `balanced_eval`, `maxFanin_balanced_le`, `depth_balanced_le`, `size_balanced_le`, `balanced_nil`, `balanced_singleton` (Combinators) |
| `bitsVal`, `prefixVal` (Adder:78/82) | CarrySave F5–F6, Compare F7–F8, ModSum F9 | `bitsVal_eq_prefixVal` Adder:136; `prefixVal_zero`/`_succ`/`_succ'`/`_lt`/`_congr` Adder:87/90/94/101/110; `prefixVal_add` Adder:397 |
| `carryBit` (Adder:377) | Compare F7 (statement only) | `prefixVal_add` Adder:397 (semantics); case readers MISSING (below) |
| `DAGGate.eval` (DAGCircuit:123) | NANDForm N1–N3, NANDLayering N7 | `DAGGate.eval_eq` DAGCircuit:131 |
| `DAGGate.depth` (DAGCircuit:139) | NANDForm N2, N5; NANDLayering N8, N10 | `DAGGate.depth_eq` DAGCircuit:571; `DAGGate.getD_lt_depth` DAGCircuit:580 |
| `DAGCircuit.eval`, `values` (DAGCircuit) | N3, N7; C22 | `DAGCircuit.eval_eq` DAGCircuit:486; `values_eq` :478; `values_getD_input` :536; `values_getD_gate` :547 |
| `DAGCircuit.depth`, `depthAt`, `depths` (DAGCircuit) | `IsLayered`, `layerColumn` (called, not unfolded); N5, N8, N10, N11; C22 | `depth_eq` :609; `depthAt_eq` :605; `depths_eq` :601; `depthAt_input` :542; `depthAt_gate` :557 |
| `DAGCircuit.size` (DAGCircuit:502) | N6, N11 | `size_eq` DAGCircuit:505 |
| `runWith` (DAGCircuit:149) | N2, N7, N8 (through the readers below) | `runWith_nil`/`_cons`/`_append`/`_singleton`, `length_runWith`, `runWith_getD_of_lt`/`_gate`/`_take` (DAGCircuit) |
| `vertexValue`, `vertexDepth` (TreeDAG:53/57) | N2 | `vertexValue_append`/`_last`/`_input`, `vertexDepth_append`/`_last`/`_input` TreeDAG:63–102 |
| `DAGCircuit.rewrite` (DAGTransform:246) | `toNANDForm` (applied, not unfolded); N3–N6 | `rewrite_eval` :263, `rewrite_depth_le` :269, `rewrite_new_gates` :273, `rewrite_length_le` :278 |
| `GadgetSpec` (DAGTransform:55, a structure) | N2 | its constructor and fields (projections) |
| `GatesAcyclic` (DAGCircuit:395) | N12 (sketch) | `GatesAcyclic.nil`/`.snoc`/`.append` :399–415; `gatesAcyclic_nil`/`_cons`/`_append` :426/431/448 (all produce or consume `GatesAcyclic`; none unfolds it: see MISSING) |
| `DAGCircuit.IsFaninTwo` (DAGCircuit:512) | C22 | `isFaninTwo_iff` DAGCircuit:519 |
| `DAGCircuit.toTree` (TreeDAG:404) | C22 | `toTree_eval` :594, `toTree_depth_le` :623, `toTree_maxFanin_le` :645 |
| `TreeCircuit.toDAG` (TreeDAG:349) | C24 (through `InTreeNC.inNC`) | `toDAG_eval` :357, `toDAG_size_le` :363, `toDAG_depth_le` :368, `toDAG_isFaninTwo` :378 |
| `Language.InNC` (NCAC:55) | C23–C25 | only through `Language.InNC.inTreeNC_one` NCAC:194, `Language.InTreeNC.inNC` NCAC:149, `Language.inNC_one_iff` NCAC:229 |
| `TreeCircuitFamily.language` (TreeNCAC:103) | C23–C24 | `TreeCircuitFamily.mem_language_iff` TreeNCAC:108 |
| `BranchingProgram` model (Defs, new owner) | Eval, Barrington, BarringtonConverse, NC1 | `yield_eq`, `length_eq`, `append_instrs`, `conj_eq`, `complementLast_eq`/`_nil`/`_concat`, `Instr.eval_eq`, `isPermutation_iff`, `Instr.isPermutation_iff`, `ofPerm_*`, `mem_language_iff`, `language_eq`, `isPolyLength_iff`, `inBWBP_iff`, `inPBP_iff` |
| `evalWith`, `Instr.stepWith` (Eval) | GSW G2 (6b) | `evalWith_eq`, `Instr.stepWith_apply` |
| `IsNAND`, `IsNANDForm` (NANDForm, new owner) | NANDLayering N7, N9 | `DAGGate.isNAND_iff`, `DAGCircuit.isNANDForm_iff`, N1 `eval_of_isNAND` |
| FormulaArith cross-file definitions | Compare, ModSum | the `_eq` readers (`val_eq`, `csaStep_eq`, `csaReduce_eq`, `csaLayer_*`, `csaLevels_*`, `bitAt_eq`, `carryOut_eq`, `constBits_eq`, `geConst_eq`, `maskedConst_eq`) and the F-lemmas |
| `Fin.append` (Mathlib) | `litInput` readers | `Fin.append_left`, `Fin.append_right` (Mathlib lemmas, used by `rw`) |
| `Equiv.Perm` coercion to functions, structure projections | Defs, Barrington | notation (projection coercions), never sealed |

## MISSING readers (owner-side proposals; none is added here, since every file named below is frozen)

| Foreign definition | Needed by | Proposed reader |
|---|---|---|
| `GadgetCorrect` (DAGTransform:68) | N2's fill (**expected**, r3 §H2) | `gadgetCorrect_iff : GadgetCorrect n c Q P emit ↔ ∀ g gs, GatesAcyclic n gs → … → GadgetSpec n c (g.args.length + 2) P g gs (emit g gs)` (`Iff.rfl`) |
| `GatesAcyclic` (DAGCircuit:395) | N12's fill and the `args_lt` field of `layerNAND`: the reason N12 is stated in the field's form (REPORT, statement changes) | `gatesAcyclic_iff : GatesAcyclic n gs ↔ ∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < n + i` (`Iff.rfl`) |
| `TreeCircuit.depth` / `maxFanin` / `size` on a literal (Basic) | F1–F3, C14, C17, C24 fills | `TreeCircuit.depth_lit : (lit l).depth = 0`, `maxFanin_lit : (lit l).maxFanin = 0`, `size_lit : (lit l).size = 1` (`rfl`) |
| `Lit.eval` (Basic:110, `@[simp] def`) | F1, F2, C13, C17 fills | `Lit.eval_eq : l.eval x = if l.sign then x l.idx else !x l.idx` (`rfl`) |
| `carryBit` (Adder:377) | F7's fill | `carryBit_zero`, `carryBit_succ` (`rfl`) |
| `DAGCircuit.IsWellFormed` (DAGCircuit:508) | C22's fill (for `toTree_*`) | `isWellFormed_iff` (`Iff.rfl`), or a circuit-level `IsFaninTwo.isWellFormed` |
| `Language.InTreeNC` (TreeNCAC:130) | C23 (destructs it), C24 (builds it) | `Language.inTreeNC_iff` (`Iff.rfl`) |
| `TreeCircuitFamily.HasFaninTwo`, `IsPolySize`, `HasPolylogDepth` (TreeNCAC:117/113/121) | C23, C24 fills | `hasFaninTwo_iff`, `isPolySize_iff`, `hasPolylogDepth_iff` (`Iff.rfl`) |
