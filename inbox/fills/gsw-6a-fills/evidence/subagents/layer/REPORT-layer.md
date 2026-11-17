# REPORT — sub-agent `layer` (U7, `NANDLayering.lean`, N7–N13)

## 1. Files, checks
- `TCSlib/Complexity/CircuitComplexity/NANDLayering.lean` in `/home/user/wt-layer` (not committed): **388 → 944 lines**
  (+556 fill: 17 private helpers + 7 bodies + refreshed sketches); max line width 100.
- Final check: `logs/NL-019.log`, **rc 0, 0 errors, 0 `declaration uses 'sorry'` warnings** (no `sorry` token in code;
  the word `sorryAx` remains only in the frozen `layerNAND` docstring).
- Snapshot: `snapshots/NANDLayering-final.lean` (also `-N12-N13`, `-all7-v1` (1051 lines, pre-compaction), `-all7-v2`).
- **Size above the ~700 hint.** The file is 944 (< 1000) but well above the lead's ~700 / r3's 150–300 fill lines.
  A first version was 1051; I compacted to 944. Where the lines go: structural part (chain lemmas, `layerAt_lt`,
  `layerColumn_struct`, `layerFold_struct`) ≈ 190; semantic part (readers, `layerChain_col`, `layerNAND_link`,
  `layerColumn_sem`, `layerFold_sem`) ≈ 300; target bodies ≈ 50. The fold-step case split (dead / input D=0 /
  input+twin+chain / gate top / gate+fan-in-0 twin+chain / gate+twin+chain) has to be done twice (structurally for
  N12, which cannot mention `layerNAND`; semantically over `layerNAND`). A further ~100–150 lines could probably be
  saved by one merged invariant stated over `runWith` of the intermediate gate lists (one case split, no prefix
  plumbing), at the cost of a rewrite; not done — say if you want it.

## 2. Targets (all proved)
| Target | Helpers used |
|---|---|
| N12 `layerGates_acyclic` | `layerFold_struct` (→ `layerColumn_struct`, `layerChain_acyclic`, `layerChain_isPrefix`, `length_layerChain_fst`, `mem_layerChain_fst`, `layerAt_lt`) |
| N13 `layerOutput_lt` | `layerFold_struct`, `layerAt_lt` |
| N7 `layerNAND_eval` | `layerFold_sem` (→ `layerColumn_sem`, `layerColumn_struct`, `layerFold_struct`, `layerChain_col`, `layerNAND_link`, `layerNAND_single`, `layerNAND_depthAt_snoc`, `layerNAND_values_snoc`, `layerNAND_values_lit`, `layerGates_isNAND`, `foldr_max_eq_of_forall`, chain lemmas) |
| N8 `layerNAND_isLayered` | `layerFold_sem`, `foldr_max_eq_of_forall` |
| N9 `layerNAND_isNANDForm` | `layerGates_isNAND` (→ `layerFold_struct`) |
| N10 `layerNAND_depth` | `layerFold_sem` |
| N11 `layerNAND_size_le` | `layerFold_struct` |

No private `def` was needed: the column invariant is stated as conclusions of `layerFold_struct` /
`layerFold_sem` (over `(List.range v).foldl C.layerColumn ([], [])`) and hypotheses/conclusions of the step lemmas.

## 3. Private helpers (17; all docstrings carry a formula and "Glue."; `hygiene.py`: 0 violations)
Namespace `BoolCircuit`. Before N12 (structural, no `layerNAND`):
1. `layerChain_isPrefix` — `gs <+: (layerChain N gs a b s).1`.
2. `length_layerChain_fst` — `(layerChain N gs a b s).1.length = gs.length + 2 * s`.
3. `mem_layerChain_fst` — `g ∈ (layerChain N gs a b s).1 → g ∈ gs ∨ ∃ w, g = ⟨.not, [w]⟩`.
4. `layerChain_acyclic` — `GatesAcyclic N gs → a < N + |gs| → b < N + |gs| → GatesAcyclic N (layerChain N gs a b s).1 ∧ ∀ w ∈ a :: b :: (layerChain N gs a b s).2, w < N + (layerChain N gs a b s).1.length`.
5. `DAGCircuit.layerAt_lt` — `0 < B → (∀ col ∈ cols, ∀ w ∈ col, w < B) → C.layerAt cols v k < B`.
6. `DAGCircuit.layerColumn_struct` (sketch) — one step: acyclic `s.1`, columns below `n+n+|s.1|`, NAND gates ⇒ `C.layerColumn s v` = `s.1` extended (`<+:`) acyclically by ≤ `2 * C.depth + 1` gates (NAND under `C.IsNANDForm`), plus one column `col` with entries `< n + n + |new gates|`.
7. `DAGCircuit.layerFold_struct` — for `s = (List.range v).foldl C.layerColumn ([], [])`: `s.2.length = v`, `GatesAcyclic (n+n) s.1`, column entries `< n + n + |s.1|`, `C.IsNANDForm → ∀ g ∈ s.1, g.IsNAND`, `s.1.length ≤ (2 * C.depth + 1) * v`.
In section `LayerNAND` before N7 (semantic):
8. `DAGCircuit.layerGates_isNAND` — `C.IsNANDForm → ∀ g ∈ C.layerGates, g.IsNAND`.
9. `foldr_max_eq_of_forall` — `(∀ y ∈ l, y = k) → y₀ ∈ l → l.foldr max 0 = k` (ℕ).
10. `DAGCircuit.layerNAND_depthAt_snoc` — `gs ++ [g] <+: C.layerNAND.gates → C.layerNAND.depthAt (n + n + gs.length) = 1 + (g.args.map C.layerNAND.depthAt).foldr max 0`.
11. `DAGCircuit.layerNAND_values_snoc` — `C.IsNANDForm → gs ++ [g] <+: C.layerNAND.gates → (C.layerNAND.values y).getD (n + n + gs.length) false = !(g.args.all fun a => (C.layerNAND.values y).getD a false)`.
12. `DAGCircuit.layerNAND_single` — for `gs ++ [⟨.not,[w]⟩] <+: C.layerNAND.gates`: `C.layerNAND.depthAt (n + n + gs.length) = C.layerNAND.depthAt w + 1` and (NAND form) value `= !value w`.
13. `DAGCircuit.layerNAND_values_lit` — `u < n →` value of input `u` on `litInput x` `= (C.values x).getD u false` and of input `n + u` `= !(C.values x).getD u false`.
14. `layerChain_col` — generic over a vertex predicate `P`: if every link lifts `P` two levels, `(layerChain N gs a b s).1 <+: G → P a L → P b (L + 1) → ∀ j ≤ s + 1, P ((a :: b :: (layerChain N gs a b s).2).getD j 0) (L + j)`.
15. `DAGCircuit.layerNAND_link` — a link `NAND[a], NAND[n+n+|gs|]` (prefix of the layering's gates): `depthAt a = L → depthAt (n + n + gs.length + 1) = L + 2`, and the value of an old vertex `u` is kept.
16. `DAGCircuit.layerColumn_sem` (sketch, Steps 1–5) — one step, over `C.layerNAND`: every copy `v@k`, `δ ≤ k ≤ D`, has depth `k` and (NAND form) the value of `v`; every new gate reads vertices of one common depth.
17. `DAGCircuit.layerFold_sem` — the fold: for `v ≤ n + |C.gates|` with the fold's gates a prefix of `C.layerNAND.gates`, every live copy `u@k` (`u < v`) has depth `k` and the value of `u`; every gate of the fold reads vertices of one common depth.

Why not existing lemmas: 1–7, 10–17 are about this file's own definitions (`layerChain`, `layerAt`, `layerColumn`, `layerNAND`) — no TCSlib lemma exists (grep). 9: Mathlib's `List.max_le_of_forall_le` / `List.le_max_of_le` (Mathlib/Data/List/MinMax.lean) are not in the import closure (NL-006 `Unknown constant`); `exact?` finds nothing (DupNL-001); TCSlib has only private inequality variants. See `searches.md`.

## 4. Readers used (foreign)
- N12/N13/N9/N11 (structural): `GatesAcyclic.nil`, `GatesAcyclic.snoc`, `gatesAcyclic_iff`, `DAGGate.isNAND_iff`, `DAGCircuit.isNANDForm_iff`, `DAGCircuit.size_eq` (N11); own `layerChain_zero/_succ`, `layerAt_eq`, `layerColumn_eq`, `layerFold_eq`, `layerGates_eq`, `layerOutput_eq`, `layerNAND_gates`.
- N7/N8/N10 (semantic): `DAGCircuit.depthAt_gate`, `DAGGate.depth_eq`, `DAGCircuit.depthAt_eq`, `DAGCircuit.depthAt_input`, `DAGCircuit.values_getD_gate`, `DAGCircuit.values_getD_input`, `DAGGate.getD_lt_depth`, `all_congr_mem`, `DAGCircuit.depth_eq`, `DAGCircuit.eval_eq`, `DAGCircuit.isNANDForm_iff`, `DAGGate.isNAND_iff`, `DAGGate.eval_of_isNAND` (**N1, frozen in-house**), fields `C.args_lt`, `C.output_lt`; own `litInput_castAdd/_natAdd`, `layerNAND_gates`, `layerNAND_output`, `isLayered_iff`.
- Rule 10 self-check: `probes/SealNL.lean` = the final file with `attribute [local irreducible]` on every foreign DAG/NAND definition (`DAGGate.eval/depth`, `runWith`, `GatesAcyclic`, `DAGCircuit.values/eval/depths/depthAt/depth/size/IsWellFormed/IsFaninTwo`, `DAGGate.WellFormed/FaninTwo/remap/IsNAND`, `constGate`, `IsNANDForm`, `nandGadget`, `toNANDForm`, `GadgetCorrect`, `rewriteStep/Gates`, `rewrite`): rc 0 (`logs/SealNL-002.log`); control `SealNLControl` (an added `C.depth = C.depthAt C.output := rfl`) fails exactly once (`logs/SealNLControl-001.log`). Not a substitute for your seals.

## 5. Axioms (`probes/AxNL.lean`, `logs/AxNL-002.log`)
- `layerGates_acyclic`, `layerOutput_lt`, **`layerNAND`, `layerNAND_gates`, `layerNAND_output`**, `layerNAND_isNANDForm`, `layerNAND_size_le`: `[propext, Classical.choice, Quot.sound]` — no `sorryAx` (G6A-F14 satisfied).
- `layerNAND_eval`, `layerNAND_isLayered`, `layerNAND_depth`: `+ sorryAx`, only through N1 `DAGGate.eval_of_isNAND` (my file has no admission). N8/N10 reach N1 only because the depth and value parts of the column invariant are proved together in `layerColumn_sem`/`layerFold_sem` (the value part uses N1); semantically they do not need it. Splitting the invariant would cost ~40+ lines; not done.

## 6. Refreshed sketches (old → new)
- **N12** old: "Induction along the fold (`layerFold_eq`, `List.foldl` over `List.range`) with the column invariant of the module docstring, part "every recorded copy lies below the current vertex count": each step (`layerColumn_eq`) appends gates that read `n + v` or `0, n` (inputs, below `n + n` by `NeZero n`), the recorded copies of earlier vertices (below the count by the invariant; the arguments `a` of gate `v - n` satisfy `a < v` by `C.args_lt`), or the gates just appended (`layerChain_succ`: the inner gate `N + |gs|` precedes the outer one).  Each appended gate's arguments are therefore below its own vertex `n + n + i`."
  new: "Induction along the fold (`layerFold_eq`, `List.range_succ`, `List.foldl_append`; private `layerFold_struct`, one step `layerColumn_struct`) with the column invariant of the module docstring, part "every recorded copy lies below the current vertex count": each step (`layerColumn_eq`) appends gates that read `n + v` or `0, n` (inputs, below `n + n` by `NeZero n`), recorded copies (below the count, `layerAt_lt`; a missing copy reads as the input `0`), or the gates just appended (`layerChain_succ`: the inner gate `N + |gs|` precedes the outer one), so `GatesAcyclic.snoc` keeps the gate list acyclic (`layerChain_acyclic`).  The field form is `gatesAcyclic_iff`."
- **N13** old: "The output's column exists because `C.depthAt C.output = C.depth` (`DAGCircuit.depth_eq`) and `C.output < n + C.gates.length` (`C.output_lt`), so the fold visits it and does not take the dead branch; its first entry is `out@D` (`layerOutput_eq`, `layerAt_eq`, index `D - D = 0`), which by the column invariant is below the vertex count `n + n + |C.layerGates|`."
  new: "The output is the recorded copy `out@D` (`layerOutput_eq`).  By the column invariant (private `layerFold_struct` at `n + |C.gates|`, `layerFold_eq`, `layerGates_eq`) every column entry lies below the vertex count `n + n + |C.layerGates|`, and so does every recorded copy (`layerAt_lt`: a missing copy reads as the input `0`, below `n + n` by `NeZero n`)."
- **N7** last sentence old: "…A chain link gives `!!b = b`.  Read off at `out@D` with `DAGCircuit.eval_eq` and `layerNAND_output`."
  new: "…A chain link gives `!!b = b`.  The induction is the private `layerFold_sem` (one step `layerColumn_sem`, links `layerChain_col`, `layerNAND_link`); read off at the live output `out@D` (`C.output_lt`, `DAGCircuit.depth_eq`) with `DAGCircuit.eval_eq`, `layerNAND_output` and `layerOutput_eq`." (text before it unchanged)
- N8, N9, N10, N11 sketches unchanged (they describe the delivered proofs).

## 7. Module docstring changes
- Admission sentence (permitted): old "range) are the targets N12–N13, as N2 is for `toNANDForm`, so while they are admitted `sorryAx` / reaches `layerNAND` through them only." → new "range) are the targets N12–N13, as N2 is for `toNANDForm`; they are proved here, structurally / (no NAND-form hypothesis, no admitted lemma), so no admission reaches `layerNAND` through them." (same 2 lines). Revert if you prefer the frozen wording.
- **G6A-F07** (optional, done): `## References` [Bar89] entry "D. A. Barrington, … J. Comput. Syst. Sci. 38(1):150–164, 1989." → "D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize / exactly those languages in NC¹*, J. Comput. System Sci. 38(1):150–164, 1989." (wording of `Barrington.lean:61–62`; the entry stays 2 lines, re-wrapped).
- "Main results: All are statement-phase targets (glue):" left unchanged. The `layerNAND` docstring ("While N12 and N13 are admitted, `sorryAx` reaches it through them only") is frozen and left as is (now stale).

## 8. Imports, overlaps, requests
- Imports added: none.
- Overlap: `foldr_max_eq_of_forall` vs Mathlib `List.max_le_of_forall_le` + `List.le_max_of_le` (Mathlib/Data/List/MinMax.lean:489, :494): those two would give it by `le_antisymm`, but the module is not imported (adding `import Mathlib.Data.List.MinMax` needs your approval and cache; then the helper body could become that 2-line `le_antisymm`, or the helper could go). Private TCSlib relatives: `TQBFHardTseitin.lean:99` `foldr_max_le`, `LogspaceUniformCanon.lean:51` `le_foldr_max` (inequalities, private, not copied).
- Promotion requests: `foldr_max_eq_of_forall` (general `List ℕ` fact) — candidate for a shared list file, or replace by the Mathlib pair above.
- Scope requests: none (every reader needed exists). No target believed false.
- Addendum A (`maxDepth_le_of_forall`, `maxFaninL_le_of_forall`): not relevant to U7; not written.

## 9. Resources
- Lean runs: 25 (NL-001…NL-019, SealNL ×2, SealNLControl ×1, AxNL ×2, DupNL ×1), all through `pool_run.py`.
- Peak memory: 1 984 944 KB (DupNL `exact?` probe); module checks ≤ 1 915 356 KB; each check ~2–7 s.
- Evidence: `/home/user/w6/evidence/subagents/layer/` (`logs/`, `probes/`, `snapshots/`, `drafts/`, `searches.md`, `progress.md`).
