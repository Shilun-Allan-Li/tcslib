# Gate 54 review: the fill gate of PR #137 (C1-WC continuation 1, `Turing.exists_inputWindowCopyTM`)

Read-only review by the maintainer's review sub-agent, 2026-10-21. It covers the external
auditor's findings (`findings.md`: **FAIL, 0 blockers, 1 major, 1 minor, 10 notes**), the pack and
its evidence, and the delivery review `campaign/fills/c1/reviews/window-cont1-r3/`. The PR head is
`lean/c1-window-fill` at `9d8ab646`. The records tree `wt-hk` moved during the review, from
`865457de` to `64e2dd9e` (#140 merged as `e2bc85eb`; gates 52, 53 and 57 recorded). The records
diffs below are against `64e2dd9e`, and they still apply at `1c06ea94`, which leaves the ledger,
the backlog and gate 54 unchanged. Every claim cites a file under `out/` (this folder's
`out/`, to be filed as `evidence/round1-review/`).

Lean ran only through `tools/leanelab.sh`, one elaboration at a time, against `oleans-l137`. The
copy-text screen ran alone, under `nice -n 10`, after `pgrep` found no other screen. My worktree
`review/gate54/wt` is detached at `9d8ab646`. It holds Option B and the facade fix, uncommitted,
with the scratch files untracked in `ReviewScratch/`. Nothing was committed, pushed or edited
outside `review/gate54/`.

## Summary

| # | Sev. | Verdict | Evidence |
|---|---|---|---|
| 1 | major | **True; the major stands, and the family is wider than reported.** `iw_patch` is `@wordPatch Bool`: token for token after renaming the binders, and equal by `rfl`. `wordPatch` is at the worker's base `96d60278`, where `StepClock`'s blob `d7e21718` is the same as at the head. The same definition is also `CounterLoop`'s private `counterPatch` and `Catalog`'s private `catalogTape`. `iw_patch_append` and `iw_patch_true` are not copies. The auditor's "4/438" is a line fraction; the ledger's own measure is 1 member of 17 declarations (5.9%), also under one fifth. | `out/patch-family.txt`, `out/patch-family-sweep.txt`, `out/patch-family-open-branches.txt`, `out/patch-family-spans.txt`, `out/patch-family-chronology.txt`, `out/census-inputs.txt`, `out/optionB/probe-axioms.out` |
| 2 | minor | **True in part.** The module docstring's labels are pre-existing lines that #137 never touched (the deferred class). The facade's line 169, which carries "C1; user decision 5 of 2026-10-13", **is a line #137 changed** ("Sorried." → "Proved."). The pack's question 7 is therefore wrong about "the facade's line". | §5; `out/minor2/` |
| 3 | note | True. Bundle SHA-256 `141d6d70…619e` (outbox = stage); 25 sections, in the order of `BUNDLE-FILES.txt`. All 25 match their sources: 23 records files byte-equal, and the 2 Lean files, unfenced, equal `9d8ab646`, with git blobs equal to the replay pins. | `out/note3-bundle.txt` |
| 4 | note | True. `repairs.diff` applied at fuzz 0 to the verbatim draft gives the 437-line `e4228201…` file; the review's landing file equals the head's InputWindow. | `out/note4/repairs-reproduction.txt` |
| 5 | note | True (restated from the code: `iw_body`, `iw_patch`, `iw_prefix`, `iw_machine`, `iw_select`; no `phaseHostTM`, one `embedEmitTM`). | head `InputWindow.lean` lines 41–47, 86–89, 117–123, 187–191, 312–315, 363 |
| 6 | note | True (the quantifier order at lines 339–341; `p ≤ \|z\|` from the `Fin` bound at line 369). | head lines 338–369 |
| 7 | note | True. **One gap:** the records keep only the empty `edge-cases.out`; the examples' source exists only in the old scratch tree. Added here, and re-run against Option B: 0 diagnostics. | `out/note7/`, `out/optionB/edge-cases-B.out` |
| 8 | note | True. Exhaustion: `d + overhead(d+1) ≤ 5d + 2\|w\| + 2 ≤ 6(d+1) + 2\|w\|`. Early end, with `r = n+1 ≤ d`: `r + overhead(r) + 1 ≤ 5r + 2\|w\| + 1 ≤ 6r + 2\|w\|`. `counterOverhead_le` and `counterOverhead_le_of_le` are as cited. | `CounterLoop.lean` lines 609–641 |
| 9 | note | True. `seal-set-S3.txt` has 16 definitions and 2 derived instances; the control output has exactly the 4 expected failures; the landing S3 output is empty. The `by decide` left at line 281 is `false ≠ true` on core `Bool`. | review `out/seal-set-S3.txt`, `out/landing-IWSeal*.out` |
| 10 | note | True. The brief probe has 57 `#check`s; the outputs give 57 and 84 results with 0 error/warning lines, both at the base and at the tip; `rule11.txt` shows no R3 row and no external private. | `out/note10.txt` |
| 11 | note | True as recorded. **Provenance:** the pack's `lint.txt` is the tip's, before #132 was merged in (Primitives at 6,886 lines; the head has 7,023). Lint at `9d8ab646` gives the same 0 FAIL, 30 WARN over 38 files. | `out/lint-build-head-9d8ab646.txt` |
| 12 | note | True. The replay script pins the 2 blobs, checks the pushed head, a clean tree, ancestry of `e9e97970` and that the Lean diff is exactly the pinned files, and chains from `oleans-l132b`. Log: 2 of 2, 0 failed, static 0. | pack `evidence/replay-l137.*` |

**Census** (ledger convention: members over the file's declarations, as gate 57 corrected it, both
sides, with spans): `Build/InputWindow` has **1 member (`iw_patch`) of 17 declarations = 5.9%**, 5
lines in the member block. That is **under one fifth**, and the file had no earlier copies, so
`workflow.md` §4 does not force a §1 item; RW-1's precedent opens one anyway. Upper bound if
`iw_patch_append`/`iw_patch_true` were counted: 3 of 17 = 17.6%, still under.

**Decision for the user** (details in §§3–4, recommendation in §8):
- **Option A, acknowledge.** Acknowledge the interval-patch family (four definitions) as debt
  IW-1, retired in the dedup window by moving `wordPatch` below `Build/Catalog`. The gate closes
  on that acknowledgment, with no Lean change except the one-line facade fix.
- **Option B, fix now.** Re-point `InputWindow` to `wordPatch` by importing `Build/StepClock`.
  It is verified: 0 errors and 0 warnings, the seal with 5 controls, the statement unchanged. It
  needs the user's authorization of the import and a 2-module replay, and the gate needs a
  round-2 re-audit.

**My recommendation is A**, with the facade fix (§8).

## 1. Major 1: exactly what duplicates what

**The definition family.** Normalized by dropping the alphabet binder, unifying `Bool`/`Γ`/`Symbol`,
writing `catalogTape` as a lambda and renaming binders in order of appearance, all four token
streams are identical (`out/patch-family.txt`). In Lean, the head's `iw_patch`, pasted verbatim
under another name, satisfies `@iw_patch_head = @wordPatch Bool := rfl`
(`out/optionB/scratch/IWBProbe.lean.txt`, exit 0). A TCSlib-wide sweep of every `def`/`abbrev`
whose body is an interval test feeding `bufferTape` finds exactly these four, and no file changed
on any of the 56 open `lean/*` branches adds a fifth (`out/patch-family-sweep.txt`,
`out/patch-family-open-branches.txt`).

| Declaration | File, visibility | Introduced | Span (docstring + code) | Prior record |
|---|---|---|---|---|
| `catalogTape` | `Build/Catalog`, private, pointwise | `0aea2108`, 2026-10-10 (§12.6 fill) | 460–464, 5 lines | none |
| `counterPatch` | `Build/CounterLoop`, private, `{Γ : Type}` | `2e99bda1`, 2026-10-10 (counter fill) | 859–862, 4 lines | backlog §2, B6 F1 record ("Dedup, for the dedup window") |
| `wordPatch` | `Build/StepClock`, **public**, `{Γ : Type*}`, with `_of_mem`/`_of_not_mem` | `6158e48f`, 2026-10-14 (B6 hosts) | 84–87, 4 lines | the specification API (user, 2026-10-16) |
| `iw_patch` | `Build/InputWindow`, private, `Bool` | `9f72288d`, 2026-10-18 (this PR) | 85–89, 5 lines | pack question 6 (2026-10-21) |

**The lemmas over `iw_patch` are not members** (no recorded or published counterpart with their
statements):
- `iw_patch_append` (`patch (v ++ [b]) = update (patch v) (head + |v|) (some b)`): the nearest
  published fact is Catalog's **public** `catalog_write_take` (`Catalog.lean` line 474, in
  `InputWindow`'s import closure). It states the same step in take form (`update (interval r of w)
  (a + r) (some w[r]) = interval (r+1) of w`), with a different statement and its own proof.
  #139's `wordPatch_append` (patch then patch adjacent = patch of the concatenation) is a
  different statement too.
- `iw_patch_true` (the patch at `replicate width true` in the counter loop's explicit form): its
  only analogue is an inline `have fill` inside `CounterLoop`'s proof (line 1387), over
  `counterPatch` and an embedding `e`. That is not a declaration.
- Nothing else among the 16 privates restates a published lemma. `iw_one` is a 2-line
  composition of `runFrom_succ_eq_step'`, `runFrom_zero` and `step_of_some`, and no other
  declaration in the tree has its statement shape. `iw_select` is one of several local
  `Fin 2 ↪ Fin k` embeddings, none of them public.

**Classification.** This is debt (failure mode 5), not a watch item. The ledger's watch items are
"design-parallel, no byte-copies", and this is a byte-copy modulo renaming. It is not a freeze
violation either. The worker reported "new copies: none", and `StepClock` was outside both its
screen population (the brief's 8 files) and its import context, with ground rule 6 forbidding the
import. The maintainer disclosed the copy before the gate (pack question 6), and no record
accepts it: no `iw_patch` occurs in the ledger, the backlog or `HANDOFF.md`. The auditor's other
sub-claims check out: the threshold does not exempt small copies (`policy.md`, Duplication:
"every instance … must be human-approved"), and the 2026-10-18 landing ruling predates the
disclosure. **Scope matters for the acknowledgment:** if the user acknowledges `iw_patch` alone,
a later auditor who notices `catalogTape` or `counterPatch` has copies outside the acknowledged
scope, which failure mode 5 makes a major again. Both options therefore record the whole family.

## 2. Census (ledger convention)

Declarations are counted as the style lint counts them, as in BW-1's corrected census
(`out/lint-build-head-9d8ab646.txt`). Spans follow the ledger's rule: attached docstring through
the last code line (`out/patch-family-spans.txt`).

| File | Members | Declarations | Fraction | Lines |
|---|---|---|---|---|
| `Build/InputWindow` (the copy in #137) | 1 (`iw_patch`) | 17 (1 public, 16 private) | **5.9%** | 5 |
| `Build/StepClock` (the public one) | 1 (`wordPatch`) | 41 (8 / 33) | 2.4% | 4 |
| `Build/CounterLoop` | 1 (`counterPatch`) | 79 (59 / 20) | 1.3% | 4 |
| `Build/Catalog` | 1 (`catalogTape`) | 505 (113 / 392) | 0.2% (in none of its row's 318) | 5 |

Copied characters by the v3 screen: none, since the identifiers differ. After renaming, each copy
is the same definition of 175 to 199 characters. No file is past one fifth, and #137 adds no
copy to any file other than `InputWindow`.

## 3. Option A: acknowledge the family as debt

**What the user decides:** acknowledge the interval-patch family (IW-1) as debt, naming its
retirement. The retirement happens in the user's dedup window, in one move with Catalog's next
edit (12.2c T3 or MIG-1), as for RW-1. `wordPatch` and its cell lemmas, with #139's
`wordPatch_append` and an explicit-form lemma, move below `Build/Catalog` (into `Simulation`
beside `FinTM.bufferTape`, or into `TuringMachine/BufferWords`, now merged with #140, which
imports only `Simulation`). Then `counterPatch`, `catalogTape` and `iw_patch` are deleted and
their uses re-pointed. `CounterLoop` cannot import `StepClock`, which imports it, so the move is
the only way to retire `counterPatch`. `InputWindow` then needs no new import, and its re-proofs
are Option B's, already verified.

**The ledger entry** (`out/optionA/ledger-IW-1.diff`, against `64e2dd9e`, applies cleanly):

```diff
--- a/campaign/duplication-ledger.md
+++ b/campaign/duplication-ledger.md
@@ -366,6 +366,40 @@
 `backlog.md` BW-1, opened and acknowledged on 2026-10-18, before gate 57's pack shipped.
 `StepBlock` is under one fifth, and #140 leaves it byte-unchanged. After the retirement, neither
 file has a member.
+
+**IW-1, the window copier's interval patch** (PR #137, `Build/InputWindow`, 2026-10-21): the
+private `iw_patch` is `Build/StepClock`'s public `wordPatch` at `Γ = Bool`: token for token after
+renaming its binders (`tape`, `head`, `v` for `ct`, `cp`, `u`), and equal by `rfl`
+(`@iw_patch = @wordPatch Bool`). One definition; no proof is copied. The same definition is also
+`Build/CounterLoop`'s private `counterPatch` and `Build/Catalog`'s private `catalogTape` (written
+pointwise), both from 2026-10-10; `wordPatch` (2026-10-14) is the public one. These four are the
+**interval-patch family**: the tree and the open branches hold no other. The B6 F1 record named
+`counterPatch` for the dedup window; `catalogTape` was not recorded before. The worker reported
+"new copies: none" (`StepClock` was outside its screen population and its import context). The
+maintainer disclosed the copy in gate 54's pack (question 6), and gate 54's finding 1 made it a
+debt major. **Not members:** `iw_patch_append` appends one cell (Catalog's public
+`catalog_write_take` states the same fact in take form, with its own proof), and `iw_patch_true`
+reads the patch at the all-true word (the `Bool` case of a step inside `CounterLoop`'s proof, not
+a declaration). **ACKNOWLEDGED (user, ⟨date⟩)**, at gate 54, for the whole family. **Cleanup
+owner and window:** the user's dedup window, through backlog §1 IW-1: `wordPatch` moves below
+`Build/Catalog` with Catalog's next edit, and the three private copies re-point to it
+(`InputWindow`'s re-proofs are verified at gate 54's review). **Census** (the primary rule, each
+member counted once per file it inhabits; declarations as the style lint counts them; lines by
+the span rule):
+- `Build/InputWindow`, a copy: **1 of 17 declarations (5.9%)** (1 public, 16 private), **5**
+  lines (`iw_patch`).
+- `Build/StepClock`, the public one: **1 of 41 (2.4%)** (8 public, 33 private), **4** lines
+  (`wordPatch`).
+- `Build/CounterLoop`: **1 of 79 (1.3%)** (59 public, 20 private), **4** lines (`counterPatch`).
+- `Build/Catalog`: **1 of 505 (0.2%)** (113 public, 392 private), **5** lines (`catalogTape`). It
+  is in none of the correspondences behind Catalog's row above, so it adds one member there.
+- Copied characters: none by the v3 screen, which pairs none of the four. After renaming, each
+  is the same definition of 175 to 199 characters.
 
+**The one-fifth rule** (`workflow.md` §4): no file of the family is past one fifth.
+`InputWindow` had no earlier copies. `Catalog` had, but #137 adds no copy to it, since
+`catalogTape` predates the delivery. The §1 item IW-1 is opened anyway, as for RW-1, and
+answered. After the retirement only `wordPatch` remains, in its new home.
+
 Any new copy in a future delivery enters through the per-delivery ledger
 and the one-fifth escalation rule of `workflow.md` §4.
```

**The backlog §1 entry** (`out/optionA/backlog-IW-1.diff`, applies cleanly):

```diff
--- a/campaign/backlog.md
+++ b/campaign/backlog.md
@@ -902,6 +902,32 @@
   past one fifth**; this item is the §1 item that `workflow.md` §4 requires for it. The
   correction adds no member, file or family to what the ruling chose: the module and its four
   restatements.
+
+### IW-1: the window copier's interval patch, a copy of `wordPatch` (user, ⟨date⟩)
+
+*Origin: gate 54 (PR #137, `Build/InputWindow`), finding 1; the maintainer disclosed it in the
+pack.*
+
+`Build/InputWindow`'s private `iw_patch` is `Build/StepClock`'s public `wordPatch` at `Γ = Bool`
+(token for token after renaming its binders, and equal by `rfl`). The brief authorized no import,
+so the worker could not cite it, and the screen pairs neither. The same definition is
+`Build/CounterLoop`'s private `counterPatch` and `Build/Catalog`'s private `catalogTape`: one
+definition in four files, `wordPatch` the public one.
+- **Acknowledged (user, ⟨date⟩)**, at gate 54, for the whole family, on condition that the
+  retirement stays on this backlog.
+- **Retirement, in the user's dedup window,** in one move. `CounterLoop` cannot import
+  `StepClock`, which imports it, and `Catalog` lies below both. So `wordPatch` and its cell
+  lemmas move below `Build/Catalog`, beside `FinTM.bufferTape` (`Simulation`, or
+  `TuringMachine/BufferWords`, merged with #140), with #139's `wordPatch_append` and an
+  explicit-form lemma. `counterPatch`, `catalogTape` and `iw_patch` are then deleted and their
+  uses re-pointed. `InputWindow` needs no new import, and its re-proofs are gate 54's option B
+  (`iw_patch_append` and `iw_patch_true` through `wordPatch_of_mem`/`_of_not_mem`, with a private
+  explicit-form reading; verified: 0 errors and 0 warnings, a seal of 19 definitions with 5
+  controls, the statement unchanged). The move edits `Build/Catalog`, so it goes with Catalog's
+  next edit (12.2c T3 or MIG-1), as RW-1 does. If `InputWindow` is wanted earlier, option B
+  lands it alone, importing `StepClock` (acyclic; the closure gains that one module).
+- **Census** (`duplication-ledger.md`, IW-1): `InputWindow` 1 of 17 declarations (5.9%),
+  `StepClock` 1 of 41, `CounterLoop` 1 of 79, `Catalog` 1 of 505; none is past one fifth.
 
 ## 2. Campaign work queued or on hold
 
```

**Gate closure.** The major is a debt major, so the user's acknowledgment, recorded in
`resolutions.md` with its scheduled resolution, closes it (`TEMPLATE.md` failure mode 5;
`workflow.md` §4). Minor 2 does not hold the gate. **Round 1 closes the gate**, with no re-audit.

**Replay.** With the facade fix, the facade alone (1 module, pin `443b21f1…`). Without it, none.

**PR body:** add under Checks: "Duplication: `iw_patch` is `Build/StepClock`'s public `wordPatch`
at `Bool` (the brief authorized no import); acknowledged by the user as debt IW-1, with its
family (`counterPatch`, `catalogTape`), retired in the dedup window." Add the facade-fix commit.

## 4. Option B: fix now (re-point `iw_patch` to `wordPatch`)

**The import.** `Build/InputWindow` and `Build/StepClock` each import only `Build/CounterLoop`.
`InputWindow` is not in `StepClock`'s closure, so the import is **acyclic**. Each closure has 21
TCSlib modules, and importing `StepClock` **adds exactly one module, `Build/StepClock` itself**
(`out/closures.txt`). `StepClock`'s source is byte-identical at `96d60278`, `2d4253e6`,
`e9e97970` and `9d8ab646` (blob `d7e21718`), and `oleans-l137` holds its olean. Downstream:
`InputWindow` is imported only by the `TuringMachine` facade, so the replay list stays
`{InputWindow, TuringMachine}`, the same 2 modules as l137.

**The change** (`out/optionB/optionB.diff`, +39/−32; it applies to `9d8ab646`):
- import `Build/StepClock`;
- delete `iw_patch`, and write `wordPatch` at its 6 term uses (`iw_prefix`, `iw_local`'s
  statement, `hpatch`, `finish`, `out` ×2);
- `iw_patch_append` and `iw_patch_true`: same names, restated over `wordPatch`, re-proved through
  `wordPatch_of_mem`/`_of_not_mem` with `FinTM.bufferTape_append`/`_eq`;
- a new private `iw_patch_eq`, a patch in explicit form, proved by the two cell lemmas. The head
  unfolds `iw_patch` at 7 sites: `simp only [iw_patch, …]` ×5 and `simp [iw_prefix, iw_patch]`
  ×1 in `iw_patch_append` (3), `iw_prefix_zero`, `iw_patch_true` and the escape `hpatch`, plus the
  `rfl` that closed the target's tape clause. Pointing those at `wordPatch` would read
  `StepClock`'s definition, which rule 10 forbids, so each is re-proved: `iw_prefix_zero` by
  `wordPatch_of_not_mem`, `hpatch` by `rw [iw_patch_eq, counterWord_length]`, and the tape clause
  by `simp only [out, iw_patch_eq, y]`.

```diff
diff --git a/TCSlib/Complexity/TuringMachine/Build/InputWindow.lean b/TCSlib/Complexity/TuringMachine/Build/InputWindow.lean
index 9e6f659d..a5b4dafb 100644
--- a/TCSlib/Complexity/TuringMachine/Build/InputWindow.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/InputWindow.lean
@@ -4,6 +4,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 Authors: Seyoon Ragavan
 -/
 import TCSlib.Complexity.TuringMachine.Build.CounterLoop
+import TCSlib.Complexity.TuringMachine.Build.StepClock
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -82,43 +83,46 @@ private theorem iw_body_blank {z : List Bool} (c : Cfg 1 Bool Bool z)
   simp only [iw_body, Bool.false_eq_true, if_false, hb,
     FinTM.controlAction_apply, moveInputPos_zero]
 
-/-- Overwrite a finite interval of a tape, leaving its exterior intact. -/
-private def iw_patch (tape : ℤ → Option Bool) (head : ℤ) (v : List Bool) :
-    ℤ → Option Bool := fun q =>
-  if head ≤ q ∧ q < head + (v.length : ℤ)
-    then FinTM.bufferTape v (q - head) else tape q
+/-- A patched tape in explicit form: the word on its interval, the original tape elsewhere.
+
+**Proof sketch.** Read each cell by `Turing.wordPatch_of_mem` or `Turing.wordPatch_of_not_mem`. -/
+private theorem iw_patch_eq (tape : ℤ → Option Bool) (head : ℤ) (v : List Bool) :
+    wordPatch tape head v = fun q =>
+      if head ≤ q ∧ q < head + (v.length : ℤ)
+        then FinTM.bufferTape v (q - head) else tape q := by
+  funext q
+  split_ifs with h
+  · exact wordPatch_of_mem tape head v h.1 h.2
+  · exact wordPatch_of_not_mem tape head v h
 
 /-- Appending a bit to the copied interval changes exactly its next cell.
 
-**Proof sketch.** At the next cell use the buffer's append equation. Inside the old interval
-that equation preserves the old symbol; outside the enlarged interval both tapes are framed. -/
+**Proof sketch.** Read both patches cell by cell. At the next cell use the buffer's append
+equation. Inside the old interval that equation preserves the old symbol; outside the enlarged
+interval both tapes are the original. -/
 private theorem iw_patch_append (tape : ℤ → Option Bool) (head : ℤ)
     (v : List Bool) (b : Bool) :
-    iw_patch tape head (v ++ [b]) =
-      Function.update (iw_patch tape head v) (head + (v.length : ℤ)) (some b) := by
+    wordPatch tape head (v ++ [b]) =
+      Function.update (wordPatch tape head v) (head + (v.length : ℤ)) (some b) := by
   funext q
+  have hlen : ((v ++ [b]).length : ℤ) = v.length + 1 := by
+    rw [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
   by_cases he : q = head + (v.length : ℤ)
   · subst q
-    rw [Function.update_self]
-    simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
-      Nat.cast_one]
-    rw [if_pos (by omega), FinTM.bufferTape_append, add_sub_cancel_left, Function.update_self]
+    rw [Function.update_self, wordPatch_of_mem _ _ _ (by omega) (by omega),
+      FinTM.bufferTape_append, add_sub_cancel_left, Function.update_self]
   · rw [Function.update_of_ne he]
     by_cases hi : head ≤ q ∧ q < head + (v.length : ℤ)
-    · simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
-        Nat.cast_one]
-      rw [if_pos hi, if_pos (by omega), FinTM.bufferTape_append,
-        Function.update_of_ne (by omega)]
-    · simp only [iw_patch, List.length_append, List.length_singleton, Nat.cast_add,
-        Nat.cast_one]
-      rw [if_neg hi, if_neg (by omega)]
+    · rw [wordPatch_of_mem _ _ _ hi.1 (by omega), wordPatch_of_mem _ _ _ hi.1 hi.2,
+        FinTM.bufferTape_append, Function.update_of_ne (by omega)]
+    · rw [wordPatch_of_not_mem _ _ _ (by omega), wordPatch_of_not_mem _ _ _ hi]
 
 /-- The body configuration after copying `r` input cells starting at input index `p`. -/
 private def iw_prefix {z : List Bool} (c : Cfg 1 Bool Bool z) (p r : ℕ)
     (hr : p + r ≤ z.length) : Cfg 1 Bool Bool z where
   state := some false
   inputPos := ⟨p + 1 + r, by omega⟩
-  workTapes := fun _ => iw_patch (c.workTapes 0) (c.workTapePos 0) ((z.drop p).take r)
+  workTapes := fun _ => wordPatch (c.workTapes 0) (c.workTapePos 0) ((z.drop p).take r)
   workTapePos := fun _ => c.workTapePos 0 + (r : ℤ)
   output := c.output
 
@@ -132,7 +136,10 @@ private theorem iw_prefix_zero {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
   · funext i q
     have hz : i = 0 := Subsingleton.elim _ _
     subst i
-    simp [iw_prefix, iw_patch]
+    simp only [iw_prefix, List.take_zero]
+    exact wordPatch_of_not_mem _ _ _ (by
+      simp only [List.length_nil, Nat.cast_zero, add_zero]
+      omega)
   · funext i
     have hz : i = 0 := Subsingleton.elim _ _
     subst i
@@ -218,10 +225,11 @@ private theorem iw_join_step {z : List Bool} (c : Cfg 2 Bool (CounterLoopState B
 
 /-- The all-true underflow word has exactly the counter loop's reported tape contents. -/
 private theorem iw_patch_true (ct : ℤ → Option Bool) (cp : ℤ) (width : ℕ) :
-    iw_patch ct cp (List.replicate width true) =
+    wordPatch ct cp (List.replicate width true) =
       fun q => if cp ≤ q ∧ q < cp + (width : ℤ) then some true else ct q := by
+  rw [iw_patch_eq]
   funext q
-  simp only [iw_patch, List.length_replicate]
+  simp only [List.length_replicate]
   split_ifs with h
   · rw [FinTM.bufferTape_eq, if_pos (by omega), List.getElem?_replicate_of_lt (by omega)]
   · rfl
@@ -242,7 +250,7 @@ private theorem iw_local {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
         counterLoopCfg (some .done)
           (iw_prefix c p n (by
             have := Nat.min_le_right (Nat.ofDigits 2 (w.map Bool.toNat)) (z.length - p)
-            omega)) (iw_patch ct cp v) cp ∧
+            omega)) (wordPatch ct cp v) cp ∧
       ∀ u < T,
         (iw_machine.runFrom (counterLoopCfg (some (.dec .run)) c ct cp) u).state ≠ some .done := by
   let d := Nat.ofDigits 2 (w.map Bool.toNat)
@@ -292,12 +300,11 @@ private theorem iw_local {z : List Bool} (c : Cfg 1 Bool Bool z) (p : ℕ)
       dsimp only [t]
       omega
     · rw [MultiTapeTM.runFrom_add, iw_join_step _ hex, hsame t le_rfl, hend, hfinal]
-      have hpatch : iw_patch ct cp (counterWord w (n + 1)) = fun q =>
+      have hpatch : wordPatch ct cp (counterWord w (n + 1)) = fun q =>
           if cp ≤ q ∧ q < cp + (w.length : ℤ) then
             FinTM.bufferTape (counterWord w (n + 1)) (q - cp)
           else ct q := by
-        funext q
-        simp only [iw_patch, counterWord_length]
+        rw [iw_patch_eq, counterWord_length]
       simp only [counter_cfg_eq, hpatch]
     · intro u hu
       by_cases hut : u < t
@@ -379,12 +386,12 @@ theorem exists_inputWindowCopyTM (k : ℕ) (j dst : Fin k) (hjd : j ≠ dst) :
     iw_local body p rfl hi hp w (c.workTapes j) (c.workTapePos j) hw y.length hn
   let start := counterLoopCfg (some (.dec .run)) body (c.workTapes j) (c.workTapePos j)
   let finish := counterLoopCfg (some .done) (iw_prefix body p y.length hbound)
-    (iw_patch (c.workTapes j) (c.workTapePos j) v) (c.workTapePos j)
+    (wordPatch (c.workTapes j) (c.workTapePos j) v) (c.workTapePos j)
   let out : Cfg k Bool (CounterLoopState Bool) z :=
     ⟨some .done, (iw_prefix body p y.length hbound).inputPos,
       Function.update (Function.update c.workTapes dst
-        (iw_patch (c.workTapes dst) (c.workTapePos dst) y)) j
-        (iw_patch (c.workTapes j) (c.workTapePos j) v),
+        (wordPatch (c.workTapes dst) (c.workTapePos dst) y)) j
+        (wordPatch (c.workTapes j) (c.workTapePos j) v),
       Function.update c.workTapePos dst (c.workTapePos dst + (y.length : ℤ)), c.output⟩
   have hstart : embedEmitCfg ι c.workTapes c.workTapePos [] start = c := by
     apply embedEmitCfg_eq
@@ -428,7 +435,7 @@ theorem exists_inputWindowCopyTM (k : ℕ) (j dst : Fin k) (hjd : j ≠ dst) :
   · simp only [he, out]
   · simp only [he, out, iw_prefix, y]
   · rw [he, ← hv]
-    rfl
+    simp only [out, iw_patch_eq, y]
   · simp only [he, out, y]
   · simp only [he, out]
   · intro u hu
```

**Verification** (all against `oleans-l137`):

| Check | Result | Evidence |
|---|---|---|
| Elaboration | **0 errors, 0 warnings**. The first run had 1 error: the tape clause's residual goal differed only by the local `let y`, fixed by adding `y` to the `simp only` set | `out/optionB/elab-2.txt` (`elab-1.txt`) |
| Axioms | target `[propext, Classical.choice, Quot.sound]`, unchanged; per declaration, only `iw_patch` (gone), `iw_patch_eq` (`[propext, Quot.sound]`) and `iw_prefix_zero` (loses `Classical.choice`) differ | `out/optionB/probe-axioms.out`, `axioms-head-vs-B.diff` |
| Definitional identity | `@iw_patch_head = @wordPatch Bool := rfl` passes | `out/optionB/scratch/IWBProbe.lean.txt` |
| Freeze | public 1 → 1; the statement is byte-identical at the base, the head and B (23 lines, sha256 `b9cf1fc7…`); private 16 → 16: removed `iw_patch`, added `iw_patch_eq`, restated over `wordPatch`: `iw_local`, `iw_patch_append`, `iw_patch_true`; body only: `iw_prefix`, `iw_prefix_zero` | `out/optionB/freeze.txt`, `statement-bytes.txt` |
| Seal (rule 10) | S4 = the review's S3 (16 definitions, 2 derived instances) **plus `Turing.wordPatch`** (19 names; `-simp Action.apply`): 0 diagnostics. Sealed with controls: exactly **5 errors, the 5 controls** (the review's 4, plus a 5th that closes only by unfolding `wordPatch`, the head's line-431 pattern). Unsealed controls: 0 | `out/optionB/seal-S4.*`, `seal-S4-control.*`, `control-unsealed.*`, `scratch/IWBSeal*.lean.txt`, `out/scripts/mkseal_b.py` |
| Rewrite/simp arguments | 20 distinct on the added lines: published `wordPatch_of_mem`/`_of_not_mem` (StepClock), `FinTM.bufferTape_append` (Simulation) and `counterWord_length` (CounterLoop); own declarations and lets (`iw_prefix`, `iw_patch_eq`, `out`, `y`); Mathlib/core. No `unfold`/`show`/`change`, and `wordPatch` is never a `simp`/`rw` argument | `out/optionB/rwargs-added.txt` |
| Rule 11 | no R3 row; every new citation is public (another module's private could not elaborate) | `out/optionB/rwargs-added.txt` |
| Screen (v3, the brief's 8 files plus `StepClock`) | head and B identical: 296 declarations, 105 pairs, 21,560 characters; empty pair diff | `out/optionB/screen-*-9.txt`, `screen-head-vs-B-9.diff` |
| Lint (`TuringMachine/Build`) | 0 FAIL, 30 WARN over 38 files; only `InputWindow`'s INFO line changes (438 → 445 lines, 1 public / 16 private) | `out/optionB/lint-build-B.txt` |
| Edge cases | the review's 4 examples over B: 0 diagnostics | `out/optionB/edge-cases-B.out` |
| Widths | 445 lines, max 99 characters | `out/optionB/widths.txt` |
| Blobs | InputWindow `a5b4dafbc1cf7a5e6ef6884657145b91b0f8e9a3`; with the facade fix, facade `443b21f1445dac017cb7de9aad5c9a891d4a168a` | `out/optionB/blobs.txt` |

**Replay consequence.** `replay-l137b`: the same 2 modules (`Build/InputWindow`, `TuringMachine`)
with the two new pins, chained from `oleans-l137` (or from `oleans-l132b`, since `StepClock` is
unchanged). `replay-l137.sh`'s precheck (the Lean diff from `e9e97970` is exactly the pinned
files) still holds. If #137 is first brought up to date with the campaign, now at `e2bc85eb`,
the replay chains from that snapshot. #140 also edits the facade, at lines 15–21 and 132–138,
far from line 169, so there is no conflict.

**What the user decides:** the import of `Build/StepClock` (the brief authorized none), and a
round-2 re-audit. Under policy §1, Layering, a leaf row now depends on the step-clock module for
one definition, until that definition moves to a light home.

**Companion records** (recommended with B; they record the pre-existing remainder of the family
for acknowledgment, separate from the gate): `out/optionB/records/ledger-IW-1-residual.diff`
and `backlog-IW-1-residual.diff`, both of which apply to `64e2dd9e`.

**PR body:** the maintainer's new commit; Freeze becomes "1 → 1 public, 0 → 16 private; one
import added, `Build/StepClock` (acyclic; the closure gains that one module)"; add a Duplication
line ("`iw_patch` retired before landing: `wordPatch` cited"); and the new replay.

## 5. Minor 2: the labels

| Text | Where | Introduced or changed by #137? | Action |
|---|---|---|---|
| 16 private docstrings | `InputWindow` | introduced; **no labels** (`out/optionB/InputWindow.head.lean`) | none |
| "(proved)" status | `InputWindow` line 28 | changed (L5); **no label** | none |
| "user decision 5 of 2026-10-13; the C1 design note §2.2 step U7 and §3.4 device (i)" | `InputWindow` lines 15–16 | **pre-existing, untouched** (identical at `96d60278`, `2d4253e6`, `e9e97970`) | deferred cleanup; optional rewording drafted |
| "the universal machine U-1" | `InputWindow` line 20 | **pre-existing, untouched** | deferred cleanup; optional rewording drafted |
| "(C1; user decision 5 of 2026-10-13). Proved." | facade line 169 | **changed** by L6 ("Sorried." → "Proved."); the label rode along | **fix now** |

**The fix** (`out/minor2/facade.diff`): the facade elaborates against `oleans-l137` with **0
diagnostics** (`out/minor2/elab-facade.txt`), and the width is unchanged (max 99). The facade's
entries cite `[AB09, …]` without a References section, as this line now does.

```diff
diff --git a/TCSlib/Complexity/TuringMachine.lean b/TCSlib/Complexity/TuringMachine.lean
index d0b04c0b..443b21f1 100644
--- a/TCSlib/Complexity/TuringMachine.lean
+++ b/TCSlib/Complexity/TuringMachine.lean
@@ -166,7 +166,7 @@ for the local modifications.
 * `Build/CounterLoop` — the counter-driven loop (§12.7) and the pattern expansion
   `expandTM` (§12.8, R8.6).
 * `Build/InputWindow` — the counter-driven copy of a bounded window of the native input onto a
-  work tape (C1; user decision 5 of 2026-10-13). Proved.
+  work tape, for the nondeterministic time hierarchy [AB09, Theorem 3.2]. Proved.
 * `Build/SeamLayout` — the step block's table and summary tapes from a captured serialization,
   the one redistribution the step-block startups cite. Sorried.
 * `Build/Scan`, `Build/InputCall`, `Build/CfgRecord` — the §12.8 rows, with the field
```

**Optional, for the deferred cleanup** (`out/minor2/moddoc-optional.diff`, against the head). It
elaborates on the head (`IWADoc`) and on top of Option B (`IWBDoc`), 0 diagnostics each
(`out/minor2/elab-moddoc-summary.txt`). `Turing.NDTM.runWith_initCfg_take` and `Turing.universal`
exist (`Nondeterministic.lean` line 630, `Universal.lean` line 114).

```diff
--- a/TCSlib/Complexity/TuringMachine/Build/InputWindow.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/InputWindow.lean
@@ -12,12 +12,12 @@
 /-!
 # The bounded input window copier
 
-A counter-driven copy of a bounded window of the native input onto a work tape (user decision 5
-of 2026-10-13; the C1 design note §2.2 step U7 and §3.4 device (i)). The universal NDTM cannot
-copy its whole input `x`, since its time bound has no `|x|` term; it copies the window
-`x.take t` instead, and the input-locality lemma `Turing.NDTM.runWith_initCfg_take` shows that
-the window is enough for `t` simulated steps. The in-place suffix device stays with the
-universal machine U-1, whose `universal` has no deadline to truncate by.
+A counter-driven copy of a bounded window of the native input onto a work tape, for the
+nondeterministic time hierarchy [AB09, Theorem 3.2]. The universal NDTM cannot copy its whole
+input `x`, since its time bound has no `|x|` term; it copies the window `x.take t` instead, and
+the input-locality lemma `Turing.NDTM.runWith_initCfg_take` shows that the window is enough for
+`t` simulated steps. The in-place suffix device belongs instead to the universal machine of
+`Turing.universal`, which has no deadline to truncate by.
 
 ## Main definitions
 
@@ -30,7 +30,7 @@
 ## References
 
 * [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
-  Cambridge University Press, 2009. (§1.2: the read-only input tape.)
+  Cambridge University Press, 2009. (§1.2: the read-only input tape; Theorem 3.2.)
 -/
 
 namespace Turing
```

## 6. Notes 3–12: anything to act on

- **Note 7.** Add the examples' source to the records (`out/note7/IWEdge.lean.txt`, sha256
  `629335f0…`): the records otherwise show only an empty output. Records only, no Lean change.
- **Note 11.** Optionally record the lint at the merged head (`out/lint-build-head-9d8ab646.txt`),
  as gate 50 did for its note 11. The totals are unchanged.
- Notes 3–6, 8–10 and 12: nothing to do. Each was re-checked (summary table).
- Seen in passing, not this gate's: with `StepClock` in the population, the screen shows
  `sc_clockTM` ↔ `counterLoopTMVia` (66%/56%). These are B6 F1 v2's two pre-disclosed controller
  pairs (backlog §2), so nothing is new.

## 7. Ready-to-paste `resolutions.md`

### Option A (`out/resolutions-optionA.md`)

```markdown
# C1-WC continuation 1, the bounded input window copier (PR #137, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #137 (`lean/c1-window-fill` at `9d8ab646`):
`Turing.exists_inputWindowCopyTM` proved in `Build/InputWindow`, a maintainer-verified fill of the
worker's repaired draft (16 private `iw_` declarations). Pack `pack.md`; bundle SHA-256
`141d6d702febba320dd1772b5eff0bbea2d2178486ceebdcd596df03a6db619e` (25 sections; folder
`54-c1-window-cont1-fill-gate/`). Replay passed (user, 2026-10-21): 2 of 2, static-equal (0).

**Round 1** (`findings.md`, verbatim; received 2026-10-21): **FAIL, 0 blockers, 1 major, 1 minor,
10 notes.** The major is a debt major. The user acknowledged it (⟨date⟩), so it closes by
`TEMPLATE.md` failure mode 5 and `workflow.md` §4. **The gate is closed.** The minor is fixed on
#137 for the one line #137 changed (⟨commit⟩), with a 1-module replay of the facade
(`replay-l137b.sh`). The module docstring's inherited labels stay with the deferred documentation
cleanup. Review: `evidence/round1-review/REVIEW.md`.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | `iw_patch` is `@wordPatch Bool`, an exact copy of a public definition already at the worker's base. The pack's "design-parallel watch item" understates it, and no human acceptance is on record. | **True; acknowledged as debt (user, ⟨date⟩), as ledger IW-1 and backlog §1 IW-1.** The copy is the whole definition: token for token after renaming the binders, and `@iw_patch = @wordPatch Bool` by `rfl` (`evidence/round1-review/patch-family.txt`, `optionB/probe-axioms.out`). `StepClock` is byte-identical at the base `96d60278` and the head. The review found the same definition twice more, as `Build/CounterLoop`'s private `counterPatch` and `Build/Catalog`'s private `catalogTape`. The tree and the open branches hold no fifth copy (`patch-family-sweep.txt`, `patch-family-open-branches.txt`). **The acknowledgment covers the four as one family.** `iw_patch_append` and `iw_patch_true` are not members, since their statements differ. The first is the append form of Catalog's public `catalog_write_take`. **Census:** `InputWindow` 1 of 17 declarations (5.9%), 5 lines; `StepClock` 1 of 41; `CounterLoop` 1 of 79; `Catalog` 1 of 505. None is past one fifth. **Retirement, in the user's dedup window:** `wordPatch` moves below `Build/Catalog` with Catalog's next edit, and the three private copies re-point to it. `InputWindow`'s re-proofs are verified now (the review's option B). The pack's question-6 classification ("design-parallel watch item") is withdrawn: watch items carry no byte-copies. |
| 2 | minor | The pack says the module and facade carry no campaign labels. The module docstring still says "user decision 5 of 2026-10-13", "C1 design note", "U7" and "U-1", and the facade "C1; user decision 5 of 2026-10-13". | **True in part; erratum; the changed line fixed.** The 16 private docstrings and the module's status line carry no labels. The module docstring's labels (lines 15–16 and 20) predate #137, which leaves them untouched, so they stay with the deferred cleanup (a rewording is drafted: `evidence/round1-review/minor2/moddoc-optional.diff`). The facade's line 169 is a line #137 changed ("Sorried." → "Proved."), and it carries the label. It now reads "for the nondeterministic time hierarchy [AB09, Theorem 3.2]" (⟨commit⟩; `minor2/facade.diff`), and the facade elaborates against `oleans-l137` with 0 diagnostics. Erratum to the pack's question 7: the assertion held for the private docstrings and the status line only. |
| 7 | note | The four boundary cases follow from the branches; the bundled example output is empty. | **Done.** The records held only the empty output. The examples' source is added (`evidence/round1-review/note7/IWEdge.lean.txt`: 4 examples over the landing file). |
| 11 | note | Screens and lint hold as recorded; the screens do not establish the absence of semantic duplication. | **Done.** The pack's lint record is the tip's, before #132 was merged in (Primitives at 6,886 lines). Lint at the merged head `9d8ab646` gives the same 0 FAIL and 30 WARN over 38 files (`evidence/round1-review/lint-build-head-9d8ab646.txt`). Finding 1 covers the semantic duplication. |
| 3–6, 8–10, 12 | notes | The bundle's integrity; the repairs; the definitions and route; the contract; the constant and first arrival; the seal; rule 11 and the probes; the elaboration and replay records. | No action. Each was re-checked (`evidence/round1-review/REVIEW.md`, table): the bundle hash, its 25 sections and the replay pins; `repairs.diff` reproducing `e4228201…` at fuzz 0; `C = 6`; the four seal controls; the 57- and 84-check probes. |

**Re-replay for the minor: ⟨pending / passed (user, date)⟩:** `replay-l137b.sh`, the facade (1
module), pin `443b21f1445dac017cb7de9aad5c9a891d4a168a`, chained from `oleans-l137`.
```

### Option B (`out/resolutions-optionB.md`)

```markdown
# C1-WC continuation 1, the bounded input window copier (PR #137, a fill gate): resolutions (round 1; round 2 pending)

**Gate:** the fill gate of PR #137 (`lean/c1-window-fill` at `9d8ab646`):
`Turing.exists_inputWindowCopyTM` proved in `Build/InputWindow`, a maintainer-verified fill of the
worker's repaired draft (16 private `iw_` declarations). Pack `pack.md`; bundle SHA-256
`141d6d702febba320dd1772b5eff0bbea2d2178486ceebdcd596df03a6db619e` (25 sections; folder
`54-c1-window-cont1-fill-gate/`). Replay passed (user, 2026-10-21): 2 of 2, static-equal (0).

**Round 1** (`findings.md`, verbatim; received 2026-10-21): **FAIL, 0 blockers, 1 major, 1 minor,
10 notes.** The major is resolved by a code change on #137 (⟨commit⟩), so **round 2 re-audits
it**. The minor is fixed in the same commit. Both changed modules are replayed again
(`replay-l137b.sh`, 2 modules). Review: `evidence/round1-review/REVIEW.md`.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | `iw_patch` is `@wordPatch Bool`, an exact copy of a public definition already at the worker's base. The pack's "design-parallel watch item" understates it, and no human acceptance is on record. | **True; fixed** in ⟨commit⟩ (`evidence/round1-review/optionB/optionB.diff`). `InputWindow` imports `Build/StepClock`, which the user authorized (⟨date⟩; the brief had no import). The import is acyclic, and the closure gains exactly that module (`closures.txt`). `iw_patch` is deleted and every use cites `wordPatch`. `iw_patch_append` and `iw_patch_true` are restated over `wordPatch` and re-proved through `wordPatch_of_mem`/`_of_not_mem`. A new private `iw_patch_eq` gives a patch's explicit form at the two places that need it: the escape endpoint, and the target's tape clause, which `rfl` had closed through `iw_patch`. **Checks** (`optionB/`), against `oleans-l137`: 0 errors and 0 warnings. The target's axioms are unchanged. Freeze: 1 → 1 public, with the statement byte-identical at the base, the head and the fix; 16 → 16 private (`iw_patch` → `iw_patch_eq`; `iw_patch_append`, `iw_patch_true` and `iw_local` restated over `wordPatch`). Seal S4 (S3 plus `wordPatch`, 19 names) passes, 5 of 5 controls bite under it, and all pass unsealed. Each rewrite/simp argument on the added lines is a published theorem, an own declaration or let, or a Mathlib/core lemma; there is no `unfold`. The nine-file screen is unchanged (296 declarations, 105 pairs, 21,560 characters), as is the lint (0 FAIL, 30 WARN over 38 files). The four edge cases give 0 diagnostics. The width is at most 99. **The rest of the family:** `Build/CounterLoop`'s private `counterPatch` and `Build/Catalog`'s private `catalogTape` are the same definition and predate #137. They are recorded as ledger IW-1 and backlog §1 IW-1 and acknowledged (user, ⟨date⟩), to retire with Catalog's next edit. |
| 2 | minor | The pack says the module and facade carry no campaign labels. The module docstring still says "user decision 5 of 2026-10-13", "C1 design note", "U7" and "U-1", and the facade "C1; user decision 5 of 2026-10-13". | **True in part; erratum; the changed line fixed** in ⟨commit⟩. The 16 private docstrings and the module's status line carry no labels. The module docstring's labels (lines 15–16 and 20) predate #137, which leaves them untouched, so they stay with the deferred cleanup (a rewording is drafted: `minor2/moddoc-optional.diff`, which elaborates on top of the fix). The facade's line 169 is a line #137 changed ("Sorried." → "Proved."), and it carries the label. It now reads "for the nondeterministic time hierarchy [AB09, Theorem 3.2]" (`minor2/facade.diff`), with 0 diagnostics. Erratum to the pack's question 7: the assertion held for the private docstrings and the status line only. |
| 7 | note | The four boundary cases follow from the branches; the bundled example output is empty. | **Done.** The examples' source is added (`note7/IWEdge.lean.txt`). Re-run over the fix, they give 0 diagnostics (`optionB/edge-cases-B.out`, `optionB/scratch/IWBEdge.lean.txt`). |
| 11 | note | Screens and lint hold as recorded; the screens do not establish the absence of semantic duplication. | **Done.** The pack's lint record predates the #132 merge. Lint at `9d8ab646` and at the fix: 0 FAIL, 30 WARN over 38 files; only `InputWindow`'s INFO line changes, from 438 to 445 lines (`lint-build-head-9d8ab646.txt`, `optionB/lint-build-B.txt`). |
| 3–6, 8–10, 12 | notes | The bundle's integrity; the repairs; the definitions and route; the contract; the constant and first arrival; the seal; rule 11 and the probes; the elaboration and replay records. | No action. Each was re-checked (`REVIEW.md`, table). Round 2 sees the fix's own seal and freeze. |

**Re-replay for the fix: ⟨pending / passed (user, date)⟩:** `replay-l137b.sh`, `Build/InputWindow`
and the facade (2 modules), pins `a5b4dafbc1cf7a5e6ef6884657145b91b0f8e9a3` and
`443b21f1445dac017cb7de9aad5c9a891d4a168a`, chained from `oleans-l137` (its upstream `StepClock`
is unchanged since the base, blob `d7e21718…`).
```

## 8. Recommendation, and what closes the gate

**Recommended: Option A, with the facade fix.**
1. **The right fix is family-wide, and it moves the definition down.** Three of the four copies
   can only retire once `wordPatch` lives below `Build/Catalog`, since `CounterLoop` cannot
   import `StepClock`. That one move retires `iw_patch` too, with no new import, and B's
   re-proofs carry over unchanged. Option B edits `InputWindow` now and leaves it importing a
   module it would not need after the move.
2. **Layering** (policy §1). B makes a leaf row import the 1,177-line step-clock module for a
   2-line definition. The auditor's own suggested fix points to a common light dependency.
3. **The debt is small and fully specified:** one definition, 5.9% of the file, a verified
   retirement, the RW-1 pattern. The user acknowledges it once, for the whole family.
4. **The cost is lower:** round 1 closes on the acknowledgment, with no round-2 audit, so #137
   can merge after a 1-module facade replay.

**Choose B instead** if the user wants #137 to land without a copy and accepts the import and a
round 2. B is verified and ready (§4). With B, the companion records still bring the family's
pre-existing remainder (`counterPatch`, `catalogTape`) to acknowledgment.

**What closes gate 54** (it is FAIL now):
- **A:** the user's acknowledgment of IW-1 (the family, its census and its scheduled
  resolution), recorded in `resolutions.md`, closes the debt major (`TEMPLATE.md` failure mode
  5). The minor does not hold the gate, so **round 1 closes** once that row is recorded. With
  the facade fix, the 1-module re-replay must pass before #137 is clear to merge.
- **B:** a code change resolves the major, so **round 2 re-audits the change** (the default). The
  gate closes when round 2 returns 0 blockers and 0 majors. The 2-module re-replay must pass, and
  the user must authorize the import.

**Not yet clear to merge:** gate 54 is FAIL. Under either option the user's decision is
outstanding, and so is a re-replay whenever a Lean change lands (the facade fix, or Option B).

## 9. Evidence index (`out/`)

- Major 1: `patch-family.txt` (normalized identity), `patch-family-sweep.txt` (TCSlib-wide),
  `patch-family-open-branches.txt` (56 branches), `patch-family-spans.txt`,
  `patch-family-chronology.txt`, `census-inputs.txt`, `widths-head.txt`, `closures.txt`,
  `lint-build-head-9d8ab646.txt`.
- Option A: `optionA/ledger-IW-1.diff`, `optionA/backlog-IW-1.diff`, `optionA/records-base.txt`,
  `resolutions-optionA.md`.
- Option B: `optionB/optionB.diff`, `optionB/optionB-with-facade.diff`,
  `optionB/InputWindow.optionB.lean`, `elab-*.txt`, `probe-axioms.*`, `axioms-head-vs-B.diff`,
  `freeze.txt`, `statement-bytes.txt`, `seal-set-S4.txt`, `seal-S4*.*`, `control-unsealed.*`,
  `rwargs-added.txt`, `screen-*`, `lint-build-B.txt`, `edge-cases-B.out`,
  `edge-examples.lean.txt`, `widths.txt`, `blobs.txt`, `scratch/` (the generated Lean inputs),
  `records/` (companion diffs), `resolutions-optionB.md`.
- Minor 2: `minor2/facade.diff`, `minor2/elab-facade.txt`, `minor2/moddoc-optional.diff`,
  `minor2/elab-moddoc-summary.txt`, `minor2/scratch/`, `minor2/TuringMachine.minor2.lean`.
- Notes: `note3-bundle.txt`, `note4/repairs-reproduction.txt`, `note7/`, `note10.txt`.
- Scripts: `scripts/` (`closures.py`, `patchfamily.py`, `freeze.py`, `mkseal_b.py`, `widths.py`,
  `moddoc.py`, `optionA.py`, `optionB_records.py`).

