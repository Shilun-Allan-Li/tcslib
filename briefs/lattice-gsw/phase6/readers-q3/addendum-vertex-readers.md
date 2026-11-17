# GSW 6a reader PR #360: addendum `vertexValue_eq`, `vertexDepth_eq` (Seyoon ruling 2026-11-17)

**Status: pushed.** The maintainer pushed `cc05f76c` (fast-forward from `3ea428fd`) after Seyoon approved. The PR #360
body is updated with an addendum section, two new rows in the readers table, the new head and the checks below. U6 now
uses `vertexDepth_eq` (fill head `b65668a90bd627e004dc61052cdce8a92601a796`).

| | |
|---|---|
| Branch | `land/gsw-6a-readers` (sparse worktree `$SP/wt-rd2`) |
| Old head (remote, confirmed) | `3ea428fd8b99ffe33cdfb8dbe8068d0eb000d032` |
| New head (pushed) | **`cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25`**: one SSH-signed commit with the two trailers |
| Diff | 1 file, **+10 / −0**: a pure insertion in `TCSlib/Complexity/CircuitComplexity/TreeDAG.lean` |

## The readers
Each reader is inserted directly after the definition it reads, in #360's style. Both are proved by `rfl`, with no
deviation; neither is `@[simp]`.

| File:line (new head) | Full name | Statement |
|---|---|---|
| `TreeDAG.lean:58` | `BoolCircuit.vertexValue_eq (gs) (x) (v)` | `vertexValue gs x v = (runWith DAGGate.eval gs (List.ofFn x)).getD v false` |
| `TreeDAG.lean:67` | `BoolCircuit.vertexDepth_eq (n) (gs) (v)` | `vertexDepth n gs v = (runWith DAGGate.depth gs (List.replicate n 0)).getD v 0` |

Each docstring reads "Reader of `X`: `formula`.  Glue."

```diff
@@ -53,10 +53,20 @@ variable {n : ℕ}
 def vertexValue (gs : List DAGGate) (x : Fin n → Bool) (v : ℕ) : Bool :=
   (runWith DAGGate.eval gs (List.ofFn x)).getD v false
 
+/-- Reader of `vertexValue`:
+`vertexValue gs x v = (runWith DAGGate.eval gs (List.ofFn x)).getD v false`.  Glue. -/
+theorem vertexValue_eq (gs : List DAGGate) (x : Fin n → Bool) (v : ℕ) :
+    vertexValue gs x v = (runWith DAGGate.eval gs (List.ofFn x)).getD v false := rfl
+
 /-- The depth of vertex `v` after running `gs` over `n` inputs. -/
 def vertexDepth (n : ℕ) (gs : List DAGGate) (v : ℕ) : ℕ :=
   (runWith DAGGate.depth gs (List.replicate n 0)).getD v 0
 
+/-- Reader of `vertexDepth`:
+`vertexDepth n gs v = (runWith DAGGate.depth gs (List.replicate n 0)).getD v 0`.  Glue. -/
+theorem vertexDepth_eq (n : ℕ) (gs : List DAGGate) (v : ℕ) :
+    vertexDepth n gs v = (runWith DAGGate.depth gs (List.replicate n 0)).getD v 0 := rfl
+
```

## Checks
All evidence is under `$SP/fill86/rd/ev/`.

- **Clash scan** (`clash.txt`; the reader job's `clash.py` with the two new names):
  - Revisions scanned:
    - tip `54597efc6d55d6fe9af92208e9e28b3799daa324`
    - #358 `a616adca`
    - #359 `73aedcda`
    - #357 `dfdc56f2` (its current head)
    - #347 `daa6e173`
    - #355 `d3c7cb00`
    - #360 `3ea428fd`
  - Result: 0 declarations share either last name component, and 0 exact clashes.
- **Build** in `$SP/olean-replay-6a-readers` (`build/summary.txt`):
  - `TreeDAG` rc 0 and `DAGTransform` rc 0, with 0 errors and 0 warnings.
  - At #360's base, `DAGTransform` is the only reader-PR owner downstream of `TreeDAG`. Basic, DAGCircuit and Adder are
    upstream, and TreeNCAC imports only Basic. So nothing else was rebuilt.
- **Axioms** (`axioms.log`): both readers use no axioms (`[]`), and `getSimpTheorems` shows neither is simp.
- **Rule 10, canonical coe-A seal on `TreeDAG`** (`rule10/`; `scripts/rule10_rd.sh`):
  - Base: `3ea428fd` on `olean-snapshot`, read only. `TreeDAG.lean` is byte-equal at `8c5875fa` and `3ea428fd`.
  - Head: `cc05f76c` on the reader tree.
  - Requests are 141 in both, with identical rows.
  - Errors are 25 in both, with the same 20 failing declarations and the same messages once line numbers are removed.
  - These failures predate this change: `TreeDAG` was not an owner of #360 before, and its old proofs (`toDAG_*`,
    `unfoldGate_*`, `toTree_*`, …) read foreign definitions. The two new readers are not among the failures.
  - `touched`: 2 ADDED, every other declaration UNCHANGED.
- **Lint:**
  - `style_lint` on `TreeDAG.lean`: 1 finding at both base and head (the old `unfoldGate_size_le` sketch finding,
    shifted by 10 lines).
  - `campaign_style_lint --check8b` on `CircuitComplexity/`: only the INFO line count changes (696 → 706 lines, 39 → 41
    public). There is no new FAIL or WARN.

## Merge-tree
`cc05f76c` merges clean with each of #358 `a616adca`, #359 `73aedcda`, #357 `dfdc56f2`, #347 `daa6e173`, #355
`d3c7cb00`, and the current tip `b5526836`.

## U6 follow-up (`fill/gsw-6a-u8-u6`)
- `8aabc21b96954905d9be376008408b8ccbc2f24a`: a signed `--no-ff` merge of `cc05f76c`.
- `b65668a90bd627e004dc61052cdce8a92601a796`: deletes the private bridge `vertexDepth_eq_getD`.
  - `depth_runWith_eq` stays private. It composes `DAGGate.depth_eq` with `vertexDepth_eq` (through `funext`), so it is
    not an instance of a single reader. It drops its in-range hypothesis and is now one line.
  - NANDForm goes from 548 to 520 lines.
- **Build:** 16/16 rc 0, with 0 errors, covering `TreeDAG` and everything downstream of it in the fill tree's closure.
  Admissions are unchanged: Combinators 0 and NANDForm 0. All rebuilt oleans have link count 1.
- **Axioms:** 120 theorem constants, standard axioms only, with no `sorryAx`.
- **Seals:** NANDForm coe-A base vs head: 180 = 180 requests, identical rows, 0 = 0 errors. `vertexDepth` is sealed.
- **Lint:** `style_lint` gives 0 findings; campaign lint has no new FAIL or WARN.
