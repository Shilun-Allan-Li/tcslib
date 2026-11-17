# Gate 45 · the GSW 6a gate: O1 (#358) and the 6a statements (#359) · round 2 · G45-01..03 fixed by LE-g45 and LE-g45b

Round 1 (Codex) was **HOLD overall: #358 CLEAR, #359 HOLD**: 0 blockers, 1 major (G45-01, #359), 1 minor (G45-03,
#359), 1 note (G45-02, #358), and no mathematical gap: all 98 targets sound as stated (`findings-r1.md`). The
maintainer's resolution is `resolutions-r1.md`: **landing edit LE-g45** (Seyoon's ruling: fix now), and the docstring
follow-up **LE-g45b**.

| Item | Pin |
|---|---|
| PR #358 (O1) head, round 2 | `a616adcac0760ab56b1b0a2a4869f4763843f9ab`, **unchanged** since round 1 (merge base `e1d39836ed4a69a34914c35f4c73c71de853dcc6`) |
| PR #359 (statements) head, round 2 | `d154c8830fc8ffc52671b41992e7dbef61e30959`, tree `be58919ee4e1aa52ab1f1441d5b52c41b6caa8d9` = round 1's `73aedcdaaaffef7e69ab012d9b9195f150bae68d` + LE-g45 `ad9c4fc701ed145cbc96acceefaad447398c8321` + LE-g45b `d154c883`; base `land/gsw-6a-o1` at `a616adca` |
| Records, round 1 | `8c5875fa268a622e4e166da5f7a992715097c2c7` |
| Records, round 2 | given in the dispatch prompt (the commit that files this pack) |
| Round-1 pack | exchange `059331913c8a5380d3ae53e5e9dffa3c7ff6e2b4`, `outbox/gates/45-gsw-6a-gate/` |

Lean paths below are under `TCSlib/Complexity/`; `BP/` is `BranchingPrograms/`, `CC/` is `CircuitComplexity/` and
`FA/` is `CircuitComplexity/FormulaArith/`. Line numbers are at `d154c883` unless stated.

## 1. The two edits

**LE-g45** (`le-g45.diff.txt` = `git diff 73aedcda ad9c4fc7`, SHA-256 `c8edd59a…`): commit `ad9c4fc7`, sole parent
`73aedcda`, SSH-signed with the records key (`SHA256:32dP45eS…2wc`, as `73aedcda`), message ending with the two trailers.
3 files, +15/−14 (`git diff --numstat`: Barrington 5/3, Combinators 10/6, Hierarchy 0/5).
- **G45-01, the move.** `BoolCircuit.eval_node_nil` (with its docstring, 5 lines) is deleted from `CC/Hierarchy.lean`
  (old `:104–108`) and inserted into `FA/Combinators.lean` (`:415`), inside `namespace BoolCircuit`, just before
  `TreeCircuit.const`. Same full name, binders (`{n : ℕ}` ambient in both files), statement and docstring.
  - **Disclosed deviation (Rule 10):** the proof changes from `cases b <;> simp [TreeCircuit.eval]` (an explicit unfold
    of `Basic`'s `TreeCircuit.eval`) to `cases b <;> simp [TreeCircuit.eval_node_true, TreeCircuit.eval_node_false]`,
    `TreeDAG`'s public readers (`Combinators` imports `TreeDAG`).
  - **Users.** `git grep` at the head finds two, both in `Hierarchy` (`:146` in `restrictCircuit_eval`, `:192` in
    `Language.zero_inTreeSize`); they resolve through `Hierarchy → TreeNCAC → Combinators`. No import changes, so no
    cycle (round 1 noted that `Combinators` cannot import `Hierarchy`).
  - **`TreeCircuit.const_eval`** (`:432`): statement byte-identical; proof `sorry` → `rw [TreeCircuit.const_eq]; exact
    eval_node_nil b x`; docstring "Glue." and the case-split sketch replaced by "This is `BoolCircuit.eval_node_nil` read
    through `const_eq`." **Admissions 98 → 97.**
  - **Home.** `eval_node_nil` was part of `Hierarchy`, an [AB09]-chapter (Arora–Barak ch. 6) file; it now lives in the
    GSW-side `FormulaArith/Combinators.lean`, upstream of both. This is the "upstream move" option of round 1's proposed
    fix; no ledger debt row is opened.
- **G45-03.** `BP/Barrington.lean:44–46` (Orders convention) and `:342–343` (C9 docstring) now call `(13254)` Bar89's
  one-based cycle notation, whose zero-based form `(0 2 1 4 3)` is what the code implements. Bar89 anchors and quotations
  unchanged.
- **G45-02.** `FA/Combinators.lean:16–18`: "promoted with its computation unchanged; its proofs carry the five
  Q2-approved Rule 10 repairs." This is on #359; #358's own sentence at `a616adca` is unchanged (#358 is not edited).

**LE-g45b** (`le-g45b.diff.txt` = `git diff ad9c4fc7 d154c883`, SHA-256 `68f62328…`): commit `d154c883`, sole parent
`ad9c4fc7`, same key and trailers. 2 files, +13/−7, **comments and docstrings only**.
- `BP/Barrington.lean`: the remaining loose "0-based" phrasings at `:23` (module docstring, `(12345)`/`(13542)`),
  `:110` (`sigma1`) and `:119` (`sigma2`) now say Bar89's one-based cycle notation, implemented in zero-based form as
  `(0 1 2 3 4)`/`(0 2 4 3 1)`. C16's "BV14 reads coordinate `1` of a 1-based state" (`:459`) is accurate and unchanged.
- `FA/Combinators.lean` `## Main results`: `const_eval` gets its own entry ("proved from `BoolCircuit.eval_node_nil`
  (an empty gate is a constant), which moved here from `Hierarchy.lean`") and leaves the "(F3; targets)" entry, which is
  now exactly the 17 remaining F3 targets.
- **Code identity:** the comment-stripped code of both files is byte-identical to `ad9c4fc7` (stripped SHA-256
  `69e55110…` Barrington, `8c8cb4c5…` Combinators); 3 mutation controls per file are caught and 1 docstring-only negative
  control stays equal.

Sizes: `Combinators` 629 → 633 → 636 lines (G6A-F06 watch, under 800), `Barrington` 463 → 465 → 468, `Hierarchy`
343 → 338.

## 2. Evidence at `d154c883` (`le-g45.md`, `le-g45b.md`, and their zips)

- **Replays** (snapshots.md job recipe, `runner.py` unmodified, one module per call, no `lake build`):
  - LE-g45 on a `cp -al` copy of `olean-replay-6a-stmt` (#359's round-1 replay, on snapshot #5) →
    `olean-replay-6a-stmt-g45`: `downorder` changed 3, down 16; plan 16 built, 1424 reused; **16/16 rc 0**, 0 errors,
    68 warnings, all `declaration uses 'sorry'`.
  - LE-g45b on a copy of that → `olean-replay-6a-stmt-g45b`: the same 16, **16/16 rc 0**, warnings equal to LE-g45's
    (14 SAME; the 2 edited files after a −3 line shift).
  - **State 1440/1440 OK** at each head (state files `0a56622f…`, `788ec08c…`); exactly the 16 rebuilt oleans have link
    count 1; snapshot #5 (LE-g45) and the parent replay trees rehash **0/0/0** at start, after the build and at the end.
  - Output maps (Mathlib excluded, 1471 entries): `3cb140cb…` (LE-g45; 3 oleans changed against round 1's tree) and
    `fa206774…` (LE-g45b; 2 changed, the docstring-bearing `Barrington` and `Combinators`).
- **Admissions 97, exact** (`admcheck.py` against `e1d39836`): Defs 11, Eval 5, Barrington 11, BarringtonConverse 11,
  NC1 5, NANDForm 6, NANDLayering 7, Combinators 23, CarrySave 7, Compare 7, ModSum 4. The delivered row map minus
  `rename_eval`, `depth_rename` and `const_eval` matches 97/97. Against round 1's (#5 re-replay) admitted set the only
  difference is `const_eval` removed; LE-g45b's set equals LE-g45's.
- **decls2 move-only:** `REMOVED Hierarchy.lean:105 BoolCircuit.eval_node_nil` and `ADDED Combinators.lean:412
  BoolCircuit.eval_node_nil` (at `ad9c4fc7`) with identical normalized statements; no CHANGED or other row.
- **Axioms:** round 1's `AxiomsStmt.lean` (source byte-identical) differs from the re-replay log in exactly 3 lines
  (`const_eval` loses `sorryAx`; `eval_node_nil` appears; the `const_eval` trace line goes). Census **545** constants
  (round 1: 544, plus `eval_node_nil`), `sorryAx` in **102** = 97 targets + the same 5 dependents; nothing non-standard.
  `AxiomsG45.lean`: `eval_node_nil`, `const_eval`, `restrictCircuit_eval`, `zero_inTreeSize` use
  `[propext, Classical.choice, Quot.sound]`. LE-g45b's probe logs and `axtrace` are byte-identical to LE-g45's.
- **Rule 10, canonical coe-A** (round 1's collector and `mkseals_coe.py`, `SEAL_CHUNK=1000`):
  - LE-g45, base `73aedcda` against head `ad9c4fc7`: `Combinators` 174/174 requests, 0/0 errors; `Barrington` 119/119,
    0/0; `Hierarchy` 355/355, **2/2**; request names equal; the base records for `Combinators` and `Barrington` equal round
    1's (#5 re-replay) records.
  - LE-g45b, head against LE-g45's head: `Combinators` 174/0 and `Barrington` 119/0, equal (sealsum `RESULT OK`);
    `Hierarchy` not re-sealed (unchanged; olean byte-identical to LE-g45's).
  - **Coe-A equal** at base and head for all three touched owners.
- **Explicit-unfold scan** (`scan1_g40.py`/`scan2.py`, three files): 0 new foreign items; one removed (the old
  `simp [TreeCircuit.eval]`); `Combinators` and `Barrington` have 0 foreign items.
- **Lint:** `campaign_style_lint TCSlib/Complexity --check8b` 25 FAIL / 390 WARN over 513 files at base and both heads,
  FAIL/WARN line sets identical; only INFO line counts change. `style_lint`: 2 pre-existing `Hierarchy:17` false
  positives, identical.
- **Merge-tree** of `ad9c4fc7` (LE-g45): clean with #360 (`cc05f76c`), #357, #347 and #355; none touches the three files.
- **Archives:** `le-g45-evidence.zip` (`983e4238…`, `SHA256SUMS` over 227 files) and `le-g45b-evidence.zip`
  (`9f41e81b…`, 150 files), each with `PROVENANCE.txt` and `tools/TOOLS.txt`.

## 3. Pre-existing item, disclosed (not introduced)

`Hierarchy`'s canonical coe-A seal fails twice in `Language.InTreeSize.inSIZE` ("Invalid `⟨...⟩` notation", "No goals"),
with **equal** errors and request sets at `73aedcda` and `ad9c4fc7`. `Hierarchy` was unchanged by the series before LE-g45
and round 1's phase 2 did not seal it, so it was not in the round-1 records. It is a Rule 10 item for the clean-up track,
like G6A-F05 (`TreeNCAC`'s two).

## 4. What carries over

- Every round-1 pass stands for the files LE-g45/LE-g45b do not touch: all of #358; and in #359 every file except
  `Barrington`, `Combinators` and `Hierarchy` (the 13 + facade files, their targets, sources, registrations and
  sketches). In the three touched files, only the edited lines are new; the rest is as round 1 audited.
- **Seals and controls:** the three touched owners were re-sealed (coe-A) as stated in §2 with equal request sets; the
  strict A/B and coe-B seals and the paired controls for them carry over on the same argument round 1 confirmed (fixed
  variant settings, equal request sets; `eval_node_nil` is a theorem, so no request changes). The 13 other downstream
  modules were rebuilt but their own sources are unchanged (13 of 16 warning lists SAME; 13
  oleans byte-identical under LE-g45, 14 under LE-g45b).
- **Records delta:** `records-r1-r2.diff.txt` is `git diff 8c5875fa <round-2 records>` over `LatticeCryptographyPlan.md`
  and `briefs/lattice-gsw/gates/45-gsw-6a/`, with the round-2 pack files themselves excluded (see the README). It shows
  the decision-log rows (Gate 45 dispatched, round 1 ruling, LE-g45, LE-g45b and unrelated campaign rows), the round-1
  pack's records copies (filed after round 1's pin, as round 1's dispatch said), `findings-r1.md`, and the LE-g45/LE-g45b
  records.
- **PR description:** `pr359-description-r2.md` is #359's body as read from GitHub at staging.

## 5. Known slips (disclosed, not fixed)

- #359's **title** still says "(98 targets)"; its body says 97.
- #359's description names `olean-replay-6a-stmt-g45b` (built on snapshot #5) as the adoptable replay. Snapshot #6 has
  since been adopted (§7), so that tree is no longer adoptable.
- `le-g45.md` and `le-g45b.md` say "nothing was committed to the records branch"; the maintainer then committed them
  (records `e4d6308a` and `659542ec`). Their text is as the jobs wrote it.
- `le-g45.md` cites Barrington `:108`/`:116` for the loose phrasings; `le-g45b.md` gives `:109`/`:117` at `ad9c4fc7` and
  `:110`/`:119` after the edit.

## 6. Questions for the audit

1. **G45-01.** Is it closed by LE-g45? Is the edit exactly the stated move (same name, binders, statement and docstring)
   plus the readers-based proof and the `const_eval` citation, with nothing else changed? Is moving the [AB09]-chapter
   lemma `eval_node_nil` from `Hierarchy` into `FormulaArith/Combinators` an acceptable home, and is the readers-based
   proof (in place of unfolding `TreeCircuit.eval`) acceptable? Is the admitted-target inventory now exactly 97?
2. **G45-02 and G45-03.** Are they closed by LE-g45's wording and LE-g45b's follow-up? Is LE-g45b comment/docstring-only,
   and is the `## Main results` update accurate?
3. **Evidence binding.** Does the evidence bind to `ad9c4fc7` and `d154c883` and support compilation, state, admissions
   97, the move-only decls2, axioms (545 / 102), equal coe-A for the three touched owners, the unfold scan, lint and the
   comment-strip identity? Is carrying over round 1's other seals, controls and passes justified for this delta?
4. Is anything new undisclosed, including the pre-existing `Hierarchy` seal failure (§3) and the slips (§5)?

## 7. Merge conditions (maintainer; not audit items)

- **Snapshot #6 is now adopted** at `8060f6b767da9e43d1c1f6d32c55b97758b80bd8`, the #357 merge
  (`briefs/pass-shelat-ch5-8/maintainer/olean-snapshot-6-adopt/`). The round-1 and LE-g45/LE-g45b replay trees were built
  on #5 without #357 and are no longer adoptable.
- #358 merges first, then #359 (retargeted); each must **re-replay on snapshot #6** before merge-time adoption.
- Out of scope as in round 1: the Q3/#360 owner-side readers, any in-house 6a fills, the external `gsw-6a-fills` job and
  its delivery on the exchange, 6b (Gate 46, bootstrapping, circular security), and [Gen09].

## 8. Findings delivery

Return `gate45-gsw-6a-r2-findings.md` as Markdown in chat: new findings numbered from **G45-04**, the status of
G45-01..03 (closed or not), counts by severity per PR, and a verdict per PR and overall: CLEAR (zero blockers and zero
majors) or HOLD.
