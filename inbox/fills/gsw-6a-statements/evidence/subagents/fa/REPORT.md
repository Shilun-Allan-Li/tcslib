# Sub-agent fa report: FormulaArith (F1–F3, F5–F10) and probe P10

*Saved by the lead from the sub-agent's hand-back message (the harness did not let the sub-agent write
this file). Content as reported; the lead's verification is in the main `REPORT.md`.*

All five files compile with 0 errors. The only `sorry`s are the 44 targets (26 + 7 + 7 + 4). No r3
statement is shown false by any probe, and the 0-failure counts below are from recorded run outputs.
Worktree `/home/user/wt-fa`, branch `sub/fa`, nothing committed.

**The lead's O1 amendment:** the two `| [] =>` line edits are applied verbatim. A difflib comparison
against the O1 copy (`Combinators.O1.lean`, with the two edits) shows insertions only: the
`## Main definitions` list (new lines 22–28), the `## Main results` list (new lines 36–40), and the
appended block (new lines 258–658, before `end BoolCircuit`). Header, imports and code are otherwise
byte-identical.

**Lock time:** probe piece P10b5 held the host lock for 8 minutes and peaked at 13.6 GB (one `#eval`
computing the depth of the M = 12, q = 61 formula). Every other P10 piece ran in 7–61 s.

## 1. Files (last check in `build.log.summary`, all rc=0 and 0 errors)

| File | Lines | Max width | `sorry` |
|---|---|---|---|
| `TCSlib/Complexity/CircuitComplexity/FormulaArith/Combinators.lean` (extended) | 659 | 99 | 26 |
| `TCSlib/Complexity/CircuitComplexity/FormulaArith/CarrySave.lean` (new) | 297 | 98 | 7 |
| `TCSlib/Complexity/CircuitComplexity/FormulaArith/Compare.lean` (new) | 238 | 100 | 7 |
| `TCSlib/Complexity/CircuitComplexity/FormulaArith/ModSum.lean` (new) | 196 | 100 | 4 |
| `TCSlib/Complexity/CircuitComplexity/FormulaArith.lean` (facade: 3 imports, 3 `## Contents` lines) | 25 | 97 | 0 |

Imports: `CarrySave` imports `Adder` and `Combinators`; `Compare` imports `CarrySave`; `ModSum`
imports `Compare` and `Mathlib.Algebra.BigOperators.Group.Finset.Defs` (already imported by existing
TCSlib files; `∑` needs it). Repo-style headers, namespace `BoolCircuit` (`TreeCircuit.*`,
`FormulaArith.*`). No attributes, `native_decide` or `axiom`. Every definition is computable and
structurally recursive (mutual recursion through the child list for `neg`/`subst`, fuel for
`csaLevels`).

## 2. Declarations

**Combinators: definitions and readers (proved by `rfl` or `congrArg`)**
- `TreeCircuit.neg`: `neg_lit`, `neg_node` (private helpers `negList`, `negList_eq_map`).
- `TreeCircuit.subst`: `subst_lit`, `subst_node` (private helpers `substList`, `substList_eq_map`).
- `TreeCircuit.rename`: `rename_eq` (`c.rename e = c.subst fun i => lit ⟨e i, true⟩`).
- `TreeCircuit.const`: `const_eq` (`node b []`).
- `and2`, `or2`, `xor2`, `xor3`, `maj3`, each with an `_eq` reader:
  `xor2 a b = or2 (and2 a b.neg) (and2 a.neg b)`, `xor3 a b c = xor2 (xor2 a b) c`,
  `maj3 a b c = or2 (and2 a b) (and2 c (or2 a b))`.

**Combinators: targets (`sorry`)**
- F1: `neg_eval`, `depth_neg`, `maxFanin_neg`.
- F2: `subst_eval`, `depth_subst_le`, `maxFanin_subst_le`, `rename_eval`, `depth_rename`.
- F3: for each of `const`, `and2`, `or2`, `xor2`, `xor3`, `maj3`: `_eval`, `depth_*_le`
  (`depth_const` is `= 1`), `maxFanin_*_le` (`maxFanin_const` is `= 0`).

**CarrySave (`BoolCircuit.FormulaArith`): definitions and readers (proved)**
- `val`: `val_eq` (`bitsVal (U.map (·.eval x))`); `csaStep`: `csaStep_eq`; `csaLayer`:
  `csaLayer_cons_cons_cons`, `csaLayer_of_length_le_two`; `csaLevels`: `csaLevels_of_le_two`,
  `csaLevels_of_two_lt` (case readers, proved through the private `csaLevelsAux_fuel`); `csaReduce`:
  `csaReduce_eq` (`Nat.repeat csaLayer (csaLevels |Us|)`, entries 0 and 1 with `getD []`).

**CarrySave: targets** — F5: `csaStep_val`, `depth_csaStep_le`, `maxFaninL_csaStep_le`;
F6: `csaReduce_val`, `depth_csaReduce_le`, `maxFaninL_csaReduce_le`, `csaLevels_le`.

**Compare: definitions and readers (proved)** — `bitAt` (`bitAt_eq`); `carryOut` (`carryOut_eq`:
generate/propagate, an OR over `j < b` of a balanced AND of `[U_j∧W_j, U_k∨W_k for j<k<b]`);
`constBits` (`constBits_eq`); `geConst` (`geConst_eq`: `p = max |U| |W| + 1`; `c = 0` gives
`const true`, `2^p < c` gives `const false`, otherwise `carryOut` of
`csaStep U W (constBits p (2^p − c))` at position `p`).

**Compare: targets** — F7: `carryOut_eval`, `carryOut_eval_le`, `depth_carryOut_le`,
`maxFanin_carryOut_le`; F8: `geConst_eval`, `depth_geConst_le`, `maxFanin_geConst_le`.

**ModSum: definitions and readers (proved)** — `maskedConst` (`maskedConst_eq`); `modSumInterval`
(`modSumInterval_eq`: `csaReduce` of the masked constants with `⌈log₂ q⌉` bits, both outputs trimmed to
`w = ⌈log₂ M⌉ + ⌈log₂ q⌉` bits, then the balanced OR over `j < max M 1` of
`and2 (geConst U W (jq+lo)) (geConst U W (jq+hi)).neg`); `modSumDepth` (`modSumDepth_eq`).

**ModSum: targets** — F9: `modSumInterval_eval`; F10: `depth_modSumInterval_le`, `modSumDepth_le`
(r3's closed form verbatim), `maxFanin_modSumInterval_le`.

Public helpers beyond r3 §H4: `csaLayer`, `constBits`, `maskedConst` (public so that their readers
can name them; each has an `_eq` reader).

## 3. Statement changes against r3

1. `⨆` replaced in `depth_subst_le` and `maxFanin_subst_le`: `⨆ i, (f i).depth` becomes
   `Finset.univ.sup fun i => (f i).depth` (same value). Reason: `SupSet ℕ` is not in Combinators'
   frozen import closure (probe `T0_Env.lean`) and the header must stay byte-identical. r3 gives no
   formula for `maxFanin_subst_le`; chosen: `≤ max c.maxFanin (Finset.univ.sup fun i => (f i).maxFanin)`.
2. `carryOut U W b` takes the position `b` as an explicit argument (r3's sketch leaves `b` free).
3. `geConst U W c` keeps r3's value shape with no hypotheses; `depth_geConst_le` (r3 names it without
   a formula): `≤ max 1 (maxDepth (U ++ W)) + 2·clog 2 (max |U| |W| + 1) + 7`, independent of `c`.
4. Formulas where r3 named only the lemma (F5, F6): `csaStep_val`:
   `val x A + val x B + val x C = val x S + val x K`; `depth_csaStep_le`:
   `maxDepth (S ++ K) ≤ max 1 (maxDepth (A ++ B ++ C)) + 4`; `csaReduce_val`: `= (Us.map (val x)).sum`;
   `depth_csaReduce_le`: `≤ max 1 (maxDepth Us.flatten) + 4·csaLevels |Us|` (the `max 1` because the
   padding `const false` has depth 1).
5. Fan-in lemmas added for every gadget and for `csaStep`, `csaReduce`, `carryOut`, `geConst`; also
   `const_eval`/`depth_const`/`maxFanin_const` (the files are foreign to each other, so these are the
   only way to reach F10's fan-in ≤ 2).
6. `modSumInterval_eval` keeps r3's hypotheses and right-hand side; only `{a q lo hi}` are implicit and
   `x` explicit. P10 finds `hlh : lo ≤ hi` unnecessary on everything tested (kept as r3 has it; the
   docstring notes it). `hhq` is needed: q = 4, a = (3, 2), [5, 6), x = (1, 1) — formula true, right
   side false. `ha` is needed: q = 3, a = (5), [2, 3), x = 1 — formula false, right side true.

## 4. Constants marked *(fix)*

- **F3 gadget depths +1, +1, +2, +4, +3**, exactly r3's (from the constructions, `neg`
  depth-preserving); over literals `#eval` gives (1, 1, 2, 4, 3); `const` has depth 1.
- **F5: +4 over `max 1 (input depth)`** (`xor3` adds 4, `maj3` adds 3, `K₀ = const false` depth 1).
- **F6: `csaLevels k ≤ 2⌈log₂ k⌉`**, settled at constant 0 instead of r3's draft +3 (with +3 the F10
  closed form would not follow from the published bound). Proof sketch in the docstring (two layers
  take `k` to at most `(4k+10)/9 ≤ ⌈k/2⌉` for `k ≥ 20`; small cases by computation; strong induction).
  Kernel `decide +kernel` for `k < 512` against the surrogate `clogS k = if k ≤ 1 then 0 else
  log2 (k−1) + 1`; `#eval` `clogS = Nat.clog 2` on `k < 5000` and the bound on `k < 100000`, 0
  failures; Python: largest excess over `2⌈log₂ k⌉` is 0 for `k < 200000`; `decide`: `csaLevels` of
  3, 4, 9, 100 is 1, 2, 4, 11.
- **F7: depth `≤ max 1 (maxDepth (U ++ W)) + 2⌈log₂ b⌉ + 3`** (replaces r3's draft
  `2⌈log₂(b+1)⌉ + 2`): items `and2`/`or2` over padded bits ≤ D + 1; inner balanced AND over ≤ b
  items adds `⌈log₂ b⌉ + 1`; outer balanced OR over b items adds `⌈log₂ b⌉ + 1`; the extra +1 is the
  slack in O1's `depth_balanced_le`.
- **F8: depth `≤ max 1 (maxDepth (U ++ W)) + 2⌈log₂ p⌉ + 7`** (`csaStep` +4, then `carryOut` at
  p = max |U| |W| + 1).
- **F10: `modSumDepth M q = 4·csaLevels M + ⌈log₂ M⌉ + 2⌈log₂(⌈log₂ M⌉ + ⌈log₂ q⌉ + 1)⌉ + 10`**
  (masked bits depth ≤ 1; `csaReduce` ≤ 1 + 4L, trimming keeps it; each `geConst` ≤
  4L + 8 + 2⌈log₂(w+1)⌉; `neg` keeps it, `and2` adds 1, the OR over `max M 1` terms adds
  ⌈log₂ M⌉ + 1). `modSumDepth_le` is r3's statement exactly and holds with room; the construction
  gives `9⌈log₂ M⌉ + 2⌈log₂(⌈log₂ q⌉+⌈log₂ M⌉+1)⌉ + 10`. Closed-form checks (`#eval`): M, q < 300,
  90000 cases, 0 failures, minimum slack 11; the tighter form, 0 failures; a sparse grid up to
  M ≈ 1.3e5, q ≈ 2^59, 3600 cases, 0 failures. Actual depth / bound: 11/14, 19/22, 30/33, 34/37,
  39/42 for (M, q) = (1,3), (3,7), (5,17), (8,31), (12,61).

No depth term is linear in the bit length (r3 §H3.3): bit lengths enter only inside `clog`; no
Shannon, DNF or truth-table step.

## 5. Reader census

Present: `TreeCircuit.eval` — `eval_lit` Basic:150, `eval_node_true_iff`/`_false_iff` Basic:155/163,
`eval_node_true`/`_false` TreeDAG:126/132; `depth`/`maxFanin` (node) — `depth_node` Basic:213,
`maxFanin_node` Basic:223; `maxDepth` — `maxDepth_nil`/`_cons` Basic:228/231, `depth_le_maxDepth`
Basic:249; `maxFaninL` — `maxFaninL_nil`/`_cons` Basic:242/245, `maxFanin_le_maxFaninL` Basic:257;
`balanced` — its O1 lemmas; `bitsVal` — `bitsVal_eq_prefixVal` Adder:136; `prefixVal` —
`prefixVal_zero`/`succ`/`succ'`/`lt`/`congr` Adder:87/90/94/101/110, `prefixVal_add` Adder:397;
cross-file FormulaArith definitions — their `_eq` readers and F-lemmas.

MISSING (proposals): `TreeCircuit.depth_lit : (lit l).depth = 0` and `TreeCircuit.maxFanin_lit :
(lit l).maxFanin = 0` in Basic; `Lit.eval_eq : l.eval x = if l.sign then x l.idx else !x l.idx`
(`Lit.eval`, Basic:110, is a `@[simp] def` with no named reader); `carryBit_zero` and `carryBit_succ`
(both `rfl`) in Adder (`carryBit` at Adder:377).

## 6. Overlap and reuse

| New | Nearest relative | Why not reused |
|---|---|---|
| `neg` | `unfoldGate` (TreeDAG:388) | works on DAG input, not tree to tree |
| `neg`, `xor2` | `xorNode`/`IsDual` (private, Parity:60/65) | not copied; re-pointed later per P6-Q6 |
| `xor3`/`maj3` | `BinArith.carry`/`sumBit` (ClassP/BinaryArith/AddSub:49/52) | Boolean functions, not formulas |
| `xor3`/`maj3` | `fullAdderGates`/`xorGates` (Adder) | DAG gate lists, not formulas |
| `val`, `carryOut` | `bitsVal`, `carryBit` | reused as the semantics |
| `geConst`, `modSumInterval` | `FormulaKit/Gate.lean`, `dnfDAG` | truth tables, excluded by r3 §H3.3 |

Searches: `grep -rnE '(def|theorem|…)\s+(TreeCircuit\.)?(neg|subst|rename|const|and2|or2|xor2|xor3|maj3|negList|substList)\b'`
(only hit `PolyExpr.subst`, another namespace);
`grep -rnE 'FormulaArith|csaLayer|csaStep|csaReduce|csaLevels|bitAt|carryOut|geConst|modSum|constBits|maskedNum'`;
`grep -rnw 'negList|substList|csaLevelsAux|maskedConst|constBits|csaLayer|bitAt|clogS'`;
`namespace .*TreeCircuit`; readers `depth_lit`, `maxFanin_lit`, `Lit.eval_*`, `carryBit_*`,
`bitsVal_*`. No clashes, no `NAnd`/`toLayered`.

## 7. Probe P10

Sources in `/home/user/wt-fa/evidence/probes/` (`P10a`, `P10b1`–`P10b5`, `P10c1`–`P10c7`, suffix
`_FormulaArith.lean`, plus `T0_Env.lean`); copies under `probes/`; logs `P10*.log` with `.summary`;
sweep generator `tools/gen_p10_sweeps.py`. `TreeCircuit.eval`, `depth`, `maxFanin` and `Nat.clog` are
well-founded, so the kernel cannot reduce them (`T0_Env`); semantics are checked by `#eval` with
recorded `(failures, cases)` counts; only `csaLevels` uses kernel `decide`. Every run passed with 0
failures.

- P10a (33 s): xor3/maj3 truth tables (8/8 each); xor2/and2/or2/const; gadget depths and fan-ins;
  `neg`/`subst`/`rename` samples; `csaStep_val` on all 3375 triples of constant words plus a literal
  triple under 64 inputs; `csaReduce` for k ≤ 9 (640 cases) with depth and fan-in; `csaLevels` closed
  form; `carryOut` against `carryBit` (1350); `carryOut_eval_le` (734); depth/fan-in (1350); `geConst`
  value and depth (4500 each); literal-word carry/geConst (384/1024); F10 closed forms.
- P10b1–b4: F9 by `TreeCircuit.eval`, exhaustive (all a with a i < q, all lo ≤ hi ≤ q, all x) for
  M ≤ 2 with q = 2..7 and M = 3 with q ≤ 4 (7680 cases at q = 4); also the hi < lo variant, F10
  depth/fan-in on every built formula (except P10b4), edge cases q ∈ {0, 1}, the two counterexamples
  of §3.6.
- P10b5: F10 on every M = 3, q = 4 formula (1600), samples for q = 5..7, and the depth table (the
  8-minute run).
- P10c1–c7 (40–55 s each): F9 for M = 3, q = 5..7, exhaustive, with the probe-only bit-parallel
  evaluator `evalMask`: 2625 (q = 5), 6048 (q = 6), 12348 (q = 7) (a, lo, hi) triples, each over all 8
  inputs; in every chunk `evalMask` is cross-checked bit by bit against `TreeCircuit.eval`
  (336/448/576 cases, 0 failures).
- Killed runs (the first single-file P10, killed after 17 min, and the long P10b attempt) are kept
  under `killed/`.

## 8. Definitions citing a `sorry` target

None. `sorryAx` reaches only the 44 targets.
