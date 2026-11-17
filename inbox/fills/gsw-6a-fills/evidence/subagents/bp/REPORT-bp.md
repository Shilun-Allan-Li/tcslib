# REPORT-bp (U4, `TCSlib/Complexity/BranchingPrograms/BarringtonConverse.lean`, C17–C21)

## 1. Files, sizes, final check
- Only file changed: `TCSlib/Complexity/BranchingPrograms/BarringtonConverse.lean` in `/home/user/wt-bp`
  (`git diff --stat`: 1 file, +289/−44). Lines 304 → 549; max line width 100 (Python `len`); no micro sign.
- Final check: `/home/user/w6/evidence/subagents/bp/logs/Conv-002.log` — rc 0, 0 errors, empty output,
  so 0 `declaration uses 'sorry'` warnings; no `sorry` token in the file.
- Snapshot: `snapshots/BarringtonConverse-all11.lean` (base copy: `snapshots/BarringtonConverse-base.lean`).

## 2. Targets (all 11 proved) and the private helpers they use
| Target | Proved | Private helpers |
|---|---|---|
| `Instr.wire_eval` | yes | none |
| `Instr.depth_wire_le` | yes | none |
| `Instr.maxFanin_wire_le` | yes | none |
| `wireComp_eval` | yes | none |
| `depth_wireComp_le` | yes | `maxDepth_le_of_forall` |
| `compTree_eval` | yes | `compTree_eval_list` |
| `depth_compTree_le` | yes | `depth_compTree_list_le` (which uses `depth_wireComp_le`) |
| `maxFanin_compTree_le` | yes | `maxFanin_compTree_list_le`, `maxFanin_wireComp_le`, `maxFaninL_le_of_forall` |
| `toFormula_eval` | yes | none (uses `compTree_eval`) |
| `depth_toFormula_le` | yes | `maxDepth_le_of_forall` (uses `depth_compTree_le`) |
| `maxFanin_toFormula_le` | yes | `maxFaninL_le_of_forall` (uses `maxFanin_compTree_le`) |

## 3. Private helpers (all in namespace `BranchingProgram`, docstring with formula + "Glue.")
1. `BranchingProgram.maxDepth_le_of_forall {cs} {d} (h : ∀ c ∈ cs, c.depth ≤ d) : TreeCircuit.maxDepth cs ≤ d`
   — exactly the Addendum A form; list induction through `maxDepth_nil`/`maxDepth_cons` only.
2. `BranchingProgram.maxFaninL_le_of_forall {cs} {d} (h : ∀ c ∈ cs, c.maxFanin ≤ d) : TreeCircuit.maxFaninL cs ≤ d`
   — Addendum A form; through `maxFaninL_nil`/`maxFaninL_cons` only.
   Searches S1, S2 (`searches.md`): no public converse of `depth_le_maxDepth`/`maxFanin_le_maxFaninL` in TCSlib;
   only private relatives `TreeNCAC.lean:215` `maxDepth_map_le`, `:226` `maxFaninL_map_le`, `TreeDAG.lean:407,420`
   (not copied). Not in Mathlib (foreign TCSlib defs). **Shared family → promotion request to `Basic.lean`.**
3. `BranchingProgram.maxFanin_wireComp_le (hF : ∀ i j, (F i j).maxFanin ≤ 2) (hG : ∀ i j, (G i j).maxFanin ≤ 2) (i k) :
   (wireComp F G i k).maxFanin ≤ 2` — about this file's own `wireComp`; no counterpart exists (the C18 targets have
   eval/depth only).
4. `BranchingProgram.compTree_eval_list : ∀ l x i j, (compTree l i j).eval x = decide ((⟨l⟩ : BranchingProgram w n).yield x i = j)`
5. `BranchingProgram.depth_compTree_list_le : ∀ l i j, (compTree l i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 l.length + 1`
6. `BranchingProgram.maxFanin_compTree_list_le : ∀ l i j, (compTree l i j).maxFanin ≤ 2`
   — 4–6 are the list-level forms of C19 (the targets are stated for `B.instrs`), by well-founded recursion on
   `l.length` mirroring `compTree` (`termination_by l => l.length`, the same `decreasing_by` as `compTree`).
   4 and 5 carry `**Proof sketch.**` paragraphs and `-- Step` comments. Name scan S5: none of the six names exists
   in `TCSlib/` or `audits/`.

## 4. Readers / foreign lemmas used, per target
- `Instr.wire_eval`: `Instr.wire_eq` (own), `Instr.eval_eq`, `TreeCircuit.const_eq`, `TreeCircuit.const_eval` (F3),
  `TreeCircuit.eval_lit`, `Lit.eval_eq`.
- `Instr.depth_wire_le`: `Instr.wire_eq`, `const_eq`, `depth_const` (F3), `depth_lit`.
- `Instr.maxFanin_wire_le`: `Instr.wire_eq`, `const_eq`, `maxFanin_const` (F3), `maxFanin_lit`.
- `wireComp_eval`: `wireComp_eq`, `and2_eq`, `and2_eval` (F3), `balanced_eval` (O1), `eval_node_false_iff`.
- `depth_wireComp_le`: `wireComp_eq`, `and2_eq`, `depth_and2_le` (F3), `depth_balanced_le` (O1), `maxDepth_nil/_cons`.
- `compTree_eval`: `compTree_nil/_singleton/_cons_cons` (own readers), `const_eq/const_eval`, `yield_nil`, `yield_append`
  (C1, frozen), `yield_eq`, `append_instrs`, `Instr.wire_eval`, `wireComp_eval`; core `List.take_append_drop`,
  `List.foldl_cons/_nil`, `Function.comp_id`, `id_eq`.
- `depth_compTree_le`: `length_eq`, `compTree_*`, `const_eq`, `depth_const`, `Instr.depth_wire_le`, `depth_wireComp_le`;
  Mathlib `Nat.clog_of_two_le`, `Nat.clog_mono_right`; core `List.length_take/_drop/_cons`.
- `maxFanin_compTree_le`: `compTree_*`, `const_eq`, `maxFanin_const`, `Instr.maxFanin_wire_le`, `wireComp_eq`, `and2_eq`,
  `maxFanin_and2_le` (F3), `maxFanin_balanced_le` (O1), `maxFaninL_nil/_cons`.
- `toFormula_eval`: `toFormula_eq`, `balanced_eval`, `eval_node_false_iff`, `eval_node_true_iff`, `compTree_eval`,
  `Finset.mem_toList`.
- `depth_toFormula_le`: `toFormula_eq`, `depth_balanced_le`, `depth_compTree_le`, `topDepth_eq`, `maxDepth_nil/_cons`;
  Mathlib `Finset.length_toList`, `Finset.card_le_univ`, `Fintype.card_fun`, `Fintype.card_fin`,
  `Nat.clog_le_iff_le_pow` (there is no `Nat.clog_le_of_le_pow` in this Mathlib), `Nat.le_pow_clog`,
  `Nat.pow_le_pow_left`, `pow_mul`.
- `maxFanin_toFormula_le`: `toFormula_eq`, `maxFanin_balanced_le`, `maxFanin_compTree_le`, `maxFaninL_nil/_cons`.
- Duplication decision (logged in progress.md): the empty gates `node b []` and binary gates `node true [a, b]` are read
  through U8's published F3 `TreeCircuit.const_eq/const_eval/depth_const/maxFanin_const` and
  `and2_eq/and2_eval/depth_and2_le/maxFanin_and2_le` (Combinators, frozen, `sorry` at the base) instead of re-deriving
  those facts inline.
- **Axiom trace** (`logs/ConvAxioms-001.log`, `logs/ConvTrace-001.log`): every target has
  `[propext, sorryAx, Classical.choice, Quot.sound]`, and `sorryAx` is reached only through admitted frozen in-house
  declarations: C1 `BranchingProgram.yield_nil`, `yield_append` and F3 `TreeCircuit.const_eval`, `depth_const`,
  `maxFanin_const`, `and2_eval`, `depth_and2_le`, `maxFanin_and2_le`. No owned declaration is admitted.
  (Note for the lead: the brief expected only C1 for U4; F3 is added by the reuse above. It is an allowed
  `FormulaArith/Combinators` admission.)
- Rule-10 self-check: a probe copy with `attribute [local irreducible]` on `Instr.eval`, `yield`, `length`, `append`,
  `instAppend`, `Lit.eval`, `maxDepth`, `maxFaninL`, `balanced`, `const`, `and2` compiles rc 0
  (`logs/ConvSeal-003.log`; `TreeCircuit.eval/depth/maxFanin` are already irreducible). No `unfold`, `dsimp`, `show`,
  no `simp [ForeignDef]`; every added `rfl` is a syntactic equality (`obtain … rfl`, `List.mem_map` witnesses).
  `compTree_eval_list` uses structure eta (`⟨(B₁ ++ B₂).instrs⟩ = B₁ ++ B₂`) and `compTree_eval` uses `⟨B.instrs⟩ = B`
  (eta, no unfolding).

## 5. Refreshed sketches (old/new; text before `**Proof sketch.**` byte-identical)
Also in `sketch-refresh.json`. The module docstring sentence "(targets admitted with `sorry`)" became "(targets proved
here)". The two helper entries are new helper docstring text, not refreshes.

### module docstring
OLD:
```
All are statements of the 6a statement phase (targets admitted with `sorry`), except the readers.
```
NEW:
```
All are statements of the 6a statement phase (targets proved here), except the readers.
```

### Instr.wire_eval
OLD:
```
**Proof sketch.** `Instr.wire_eq` and `Instr.eval_eq`; split on `ι.map0 i = j`, `ι.map1 i = j` and
`x ι.var`.  The constants evaluate by `TreeCircuit.eval_node_true_iff`/`eval_node_false_iff` on
`[]`, the literals by `TreeCircuit.eval_lit` and a reader of `Lit.eval` (missing at the base;
proposed `Lit.eval_eq : l.eval x = if l.sign then x l.idx else !x l.idx`). -/
```
NEW:
```
**Proof sketch.** `Instr.wire_eq` and `Instr.eval_eq`; split on `ι.map0 i = j`, `ι.map1 i = j` and
`x ι.var`.  The empty gates are the constants (`TreeCircuit.const_eq`) and evaluate by
`TreeCircuit.const_eval`, the literals by `TreeCircuit.eval_lit` and the reader `Lit.eval_eq`. -/
```

### Instr.depth_wire_le
OLD:
```
**Proof sketch.** `Instr.wire_eq`; an empty gate has depth 1 (`TreeCircuit.depth_node`,
`maxDepth_nil`) and a literal depth 0 (reader `TreeCircuit.depth_lit`, missing at the base and
proposed). -/
```
NEW:
```
**Proof sketch.** `Instr.wire_eq`; an empty gate is a constant (`TreeCircuit.const_eq`) of depth 1
(`TreeCircuit.depth_const`) and a literal has depth 0 (reader `TreeCircuit.depth_lit`). -/
```

### Instr.maxFanin_wire_le
OLD:
```
**Proof sketch.** `Instr.wire_eq`; an empty gate has fan-in 0 (`TreeCircuit.maxFanin_node`,
`maxFaninL_nil`) and a literal fan-in 0 (reader `TreeCircuit.maxFanin_lit`, missing at the base
and proposed). -/
```
NEW:
```
**Proof sketch.** `Instr.wire_eq`; an empty gate is a constant (`TreeCircuit.const_eq`) of fan-in 0
(`TreeCircuit.maxFanin_const`) and a literal has fan-in 0 (reader `TreeCircuit.maxFanin_lit`). -/
```

### wireComp_eval
OLD:
```
**Proof sketch.** `wireComp_eq`, `TreeCircuit.balanced_eval`, `eval_node_false` (an `any` over
`finRange w`) and `eval_node_true` on the pairs; by `hF`, `hG` the pair `j` is true iff
`f x i = j ∧ g x j = k`, and exactly `j = f x i` can be (`List.mem_finRange`). -/
```
NEW:
```
**Proof sketch.** `wireComp_eq`, the pairs as `TreeCircuit.and2` (`and2_eq`),
`TreeCircuit.balanced_eval` and `eval_node_false_iff` (some pair is true, `List.mem_map`); by
`and2_eval`, `hF`, `hG` the pair `j` is true iff `f x i = j ∧ g x j = k`, and exactly `j = f x i`
can be (`List.mem_finRange`). -/
```

### depth_wireComp_le
OLD:
```
**Proof sketch.** `wireComp_eq` and `TreeCircuit.depth_balanced_le`: each `node true [F i j, G j k]`
has depth `≤ d + 1` (`depth_node`, `maxDepth_cons`), the list has length `w`
(`List.length_map`, `List.length_finRange`), so the depth is `≤ (d + 1) + ⌈log₂ w⌉ + 1`. -/
```
NEW:
```
**Proof sketch.** `wireComp_eq` and `TreeCircuit.depth_balanced_le`: each pair
`node true [F i j, G j k] = and2 (F i j) (G j k)` has depth `≤ d + 1` (`depth_and2_le`), so the list
has `maxDepth ≤ d + 1` (`maxDepth_le_of_forall`), and it has length `w` (`List.length_map`,
`List.length_finRange`), so the depth is `≤ (d + 1) + ⌈log₂ w⌉ + 1`. -/
```

### compTree_eval
OLD:
```
**Proof sketch.** Strong induction on the length of an instruction list `l`, for the yield of
`⟨l⟩`: the empty list by `compTree_nil` and `yield_nil`; one instruction by `compTree_singleton`,
`Instr.wire_eval` and `yield_eq`; otherwise `compTree_cons_cons`, `wireComp_eval` with the
induction hypothesis for both halves, and `yield_append` on `l = l.take m ++ l.drop m`
(`List.take_append_drop`, `append_instrs`). -/
```
NEW:
```
**Proof sketch.** The helper `compTree_eval_list`, for an arbitrary instruction list `l` and the
yield of `⟨l⟩`, by well-founded recursion on the length of `l` (as `compTree` itself): the empty
list by `compTree_nil`, `const_eval` and `yield_nil`; one instruction by `compTree_singleton`,
`Instr.wire_eval` and `yield_eq`; otherwise `compTree_cons_cons`, `wireComp_eval` with the
recursive calls for both halves, and `yield_append` on `⟨l⟩ = ⟨l.take m⟩ ++ ⟨l.drop m⟩`
(`List.take_append_drop`, `append_instrs`); then `l = B.instrs`. -/
```

### depth_compTree_le
OLD:
```
**Proof sketch.** Strong induction on the length `l` of the instruction list (with `length_eq`):
`compTree_nil`, `compTree_singleton` with `Instr.depth_wire_le` give depth `≤ 1`; for `l ≥ 2`,
`compTree_cons_cons` and `depth_wireComp_le` with the induction hypothesis for both halves
(`List.length_take`, `List.length_drop`), `Nat.clog_mono_right` and
`Nat.clog_of_two_le` (`⌈log₂ l⌉ = ⌈log₂ ⌈l/2⌉⌉ + 1`). -/
```
NEW:
```
**Proof sketch.** `length_eq` and the helper `depth_compTree_list_le`, by well-founded recursion on
the length `l` of the instruction list: `compTree_nil` (`depth_const`), `compTree_singleton` with
`Instr.depth_wire_le` give depth `≤ 1`; for `l ≥ 2`, `compTree_cons_cons` and `depth_wireComp_le`
with the recursive calls for both halves of length `≤ ⌈l/2⌉` (`List.length_take`,
`List.length_drop`), `Nat.clog_mono_right` and `Nat.clog_of_two_le`
(`⌈log₂ l⌉ = ⌈log₂ ⌈l/2⌉⌉ + 1`). -/
```

### maxFanin_compTree_le
OLD:
```
**Proof sketch.** Strong induction on the length as for `compTree_eval`: the leaves by
`compTree_nil` (`maxFanin_node`) and `Instr.maxFanin_wire_le`; a composition circuit by
`wireComp_eq`, `TreeCircuit.maxFanin_balanced_le` and `maxFanin_node` on the binary `∧` nodes. -/
```
NEW:
```
**Proof sketch.** The helper `maxFanin_compTree_list_le`, by well-founded recursion on the length
as for `compTree_eval`: the leaves by `compTree_nil` (`maxFanin_const`) and
`Instr.maxFanin_wire_le`; a composition circuit by the helper `maxFanin_wireComp_le`
(`wireComp_eq`, `TreeCircuit.maxFanin_balanced_le` and `maxFanin_and2_le` on the binary `∧`
nodes). -/
```

### toFormula_eval
OLD:
```
**Proof sketch.** `toFormula_eq`, `TreeCircuit.balanced_eval`, `eval_node_false` (an `any` over
`F.toList`, `Finset.mem_toList`) and `eval_node_true` (an `all` over `finRange w`); by
`compTree_eval` the conjunction for `f` holds iff `∀ i, B.yield x i = f i`, i.e.
`B.yield x = f` (`funext`). -/
```
NEW:
```
**Proof sketch.** `toFormula_eq`, `TreeCircuit.balanced_eval`, `eval_node_false_iff` (some `f` of
`F.toList`, `Finset.mem_toList`) and `eval_node_true_iff` (every `i` of `finRange w`); by
`compTree_eval` the conjunction for `f` holds iff `∀ i, B.yield x i = f i`, i.e.
`B.yield x = f` (`funext`). -/
```

### depth_toFormula_le
OLD:
```
(`Nat.clog_mono_right`, `Nat.clog_le_of_le_pow` with `w^w ≤ (2^⌈log₂ w⌉)^w`, `Nat.le_pow_clog`);
`topDepth_eq` closes the arithmetic. -/
```
NEW:
```
(`Nat.clog_le_iff_le_pow` with `|F| ≤ w^w ≤ (2^⌈log₂ w⌉)^w`, `Fintype.card_fin`,
`Nat.le_pow_clog`, `Nat.pow_le_pow_left`, `pow_mul`); the members' depth bounds pass to the lists
by `maxDepth_le_of_forall`; `topDepth_eq` closes the arithmetic. -/
```

### maxFanin_toFormula_le
OLD:
```
**Proof sketch.** `toFormula_eq`, `TreeCircuit.maxFanin_balanced_le` twice, and
`maxFanin_compTree_le` for the leaves (`maxFaninL` of a mapped list). -/
```
NEW:
```
**Proof sketch.** `toFormula_eq`, `TreeCircuit.maxFanin_balanced_le` twice, and
`maxFanin_compTree_le` for the leaves (`maxFaninL` of a mapped list, by `maxFaninL_le_of_forall`).
-/
```

### helper compTree_eval_list (new docstring part)
OLD:
```
/-- The composition tree of an instruction list `l` computes the yield of the program `⟨l⟩`:
`(compTree l i j).eval x = decide ((⟨l⟩ : BranchingProgram w n).yield x i = j)`.  Glue. -/
```
NEW:
```
/-- The composition tree of an instruction list `l` computes the yield of the program `⟨l⟩`:
`(compTree l i j).eval x = decide ((⟨l⟩ : BranchingProgram w n).yield x i = j)`.  Glue.

**Proof sketch.** Well-founded recursion on `l.length`, following `compTree`.  Empty list:
`compTree_nil`, `const_eq`/`const_eval` and `yield_nil`.  One instruction: `compTree_singleton`,
`Instr.wire_eval`, and `yield_eq` with `List.foldl` on `[ι]`.  Otherwise (Step 1) `⟨l⟩` is
`⟨l.take m⟩ ++ ⟨l.drop m⟩` (`append_instrs`, `List.take_append_drop`), so (Step 2)
`compTree_cons_cons`, `yield_append` and `wireComp_eval` with the recursive calls close it. -/
```

### helper depth_compTree_list_le (new docstring part)
OLD:
```
/-- The composition tree of an instruction list `l` has depth logarithmic in `|l|`:
`(compTree l i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 l.length + 1`.  Glue. -/
```
NEW:
```
/-- The composition tree of an instruction list `l` has depth logarithmic in `|l|`:
`(compTree l i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 l.length + 1`.  Glue.

**Proof sketch.** Well-founded recursion on `l.length`, following `compTree`.  The leaves have
depth `≤ 1` (`depth_const`, `Instr.depth_wire_le`).  For `L = |l| ≥ 2`: (Step 1)
`⌈log₂ L⌉ = ⌈log₂ ⌈L/2⌉⌉ + 1` (`Nat.clog_of_two_le`); (Step 2) both halves have length
`≤ ⌈L/2⌉` (`List.length_take`, `List.length_drop`), so by the recursive calls and
`Nat.clog_mono_right` their wires have depth `≤ (⌈log₂ w⌉ + 2)·⌈log₂ ⌈L/2⌉⌉ + 1`; (Step 3)
`depth_wireComp_le` adds `⌈log₂ w⌉ + 2`. -/
```

## 6. Imports added
- `import Mathlib.Data.Fintype.BigOperators` (after `import Mathlib.Data.Fintype.Defs`), **approved by the lead**
  (`scope-request/IMPORT-REQUEST-bp-1.md`, `…APPROVAL.md`). Reason: reuse `Fintype.card_fun` (with `Finset.card_le_univ`,
  `Fintype.card_fin` and the Pi `Fintype` instance) for `|F| ≤ w^w` in C21; at the base the closure had no
  `Fintype (Fin w → Fin w)` (Conv-001.log). Already a root of the fetched cache.

## 7. Overlaps, promotion and scope requests, false targets
- Overlap: `maxDepth_le_of_forall`/`maxFaninL_le_of_forall` relate to private `TreeNCAC.lean:215`/`:226`
  (`maxDepth_map_le`, `maxFaninL_map_le`: the same bound for a mapped list) and are the converses of public
  `Basic.lean:265` `depth_le_maxDepth` and `:273` `maxFanin_le_maxFaninL`; private elsewhere, so not reusable.
- **Promotion request:** the Addendum A family `maxDepth_le_of_forall`, `maxFaninL_le_of_forall` → `Basic.lean`.
- `maxFanin_wireComp_le` and the three `*_list` helpers are specific to this file (no promotion).
- Scope requests: only the import above (approved). No missing reader. No target is false.

## 8. Resources
- Lean runs: 9 (Conv-001, Conv-002; probes ConvImport-001/002, ConvSeal-001/002/003, ConvAxioms-001, ConvTrace-001),
  all through the pool. Peak maxrss 1,860,404 kB (ConvImport-001). Each run 2–4 s.
- Probe sources: `evidence/subagents/bp/probes/` (also `/home/user/wt-bp/probes/`, untracked).
