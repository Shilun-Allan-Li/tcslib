# GSW 6a: owner-side reader PR (Q3): build and checks

**Verdict: PASS. Draft PR #360 is open.**

| | |
|---|---|
| Branch | `land/gsw-6a-readers` |
| Head | **`3ea428fd8b99ffe33cdfb8dbe8068d0eb000d032`** (tree `5d1f4768b9825f628147e25e9c1cfb31bc309eaa`) |
| Base | records tip `8c5875fa268a622e4e166da5f7a992715097c2c7` (`origin/cryptography/pass-shelat-ch2-4`, unchanged at the end of the run) |
| Diff | one commit, 5 files, **+69 / −0**, pure insertions |
| PR | #360, draft, into `cryptography/pass-shelat-ch2-4` |

- **Scope:** G6A-F03, ruled Q3 A by Seyoon on 2026-11-17 (decision log "6a Q1–Q4"; overnight ruling 2026-11-17).
- **Run:** 2026-11-17, 09:50–10:20 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence:** `gsw-6a-readers-q3-evidence.zip`, beside this file. The zip holds its own `SHA256SUMS` and
  `PROVENANCE.txt`, and the zip's SHA-256 is in `evidence-SHA256SUMS`.
- **Not done:** nothing is committed to the records branch. This file and the zip are left uncommitted for the
  maintainer.

## 1. The readers

Each reader is inserted directly after the definition it reads.

| File:line (head) | Full name | Proof | Used by (sketch) |
|---|---|---|---|
| `Basic.lean:114` | `BoolCircuit.Lit.eval_eq` | `rfl` | F1, F2, C13, C17 |
| `Basic.lean:217` | `BoolCircuit.TreeCircuit.depth_lit` | `simp [TreeCircuit.depth]` | F1–F3, C14, C17, F9 |
| `Basic.lean:221` | `BoolCircuit.TreeCircuit.size_lit` | `simp [TreeCircuit.size]` | C24 |
| `Basic.lean:225` | `BoolCircuit.TreeCircuit.maxFanin_lit` | `simp [TreeCircuit.maxFanin]` | F1–F3, C17 |
| `Adder.lean:382` | `BoolCircuit.carryBit_zero` | `rfl` | F7 |
| `Adder.lean:386` | `BoolCircuit.carryBit_succ` | `rfl` | F7 |
| `DAGCircuit.lean:400` | `BoolCircuit.gatesAcyclic_iff` | `Iff.rfl` | N12 (field form, Q4 A), N2 |
| `DAGCircuit.lean:519` | `BoolCircuit.DAGCircuit.isWellFormed_iff` | `Iff.rfl` | C22 |
| `DAGTransform.lean:76` | `BoolCircuit.gadgetCorrect_iff` | `Iff.rfl` | N2 |
| `TreeNCAC.lean:118` | `BoolCircuit.TreeCircuitFamily.isPolySize_iff` | `Iff.rfl` | C24 |
| `TreeNCAC.lean:127` | `BoolCircuit.TreeCircuitFamily.hasFaninTwo_iff` | `Iff.rfl` | C23, C24 |
| `TreeNCAC.lean:136` | `BoolCircuit.TreeCircuitFamily.hasPolylogDepth_iff` | `Iff.rfl` | C23, C24 |
| `TreeNCAC.lean:152` | `Language.inTreeNC_iff` | `Iff.rfl` | C23, C24 |

- **Forms:** each statement is the census's proposed form, which is the body of the definition verbatim.
- **Docstrings:** each reads "Reader of `X`: `formula`.  Glue.", with no source tag, following the 6a statement
  files' readers (`isPolyLength_iff`, `inPBP_iff`, `litInput_eq`).
- **Binders** follow the readers already beside each definition:
  - `gatesAcyclic_iff` has implicit `{n} {gs}`, like `gatesAcyclic_cons`.
  - `isWellFormed_iff` and the family readers take the section variable `C` explicitly, like `isFaninTwo_iff` and
    `mem_language_iff`. `hasPolylogDepth_iff` takes `(d)`.
  - `Language.inTreeNC_iff (d) (L)` is explicit, like `Language.inPPoly_iff` and `inPBP_iff`.
  - `gadgetCorrect_iff` has implicit `{c Q P emit}` and the section's `{n}`.
- **None is `@[simp]`.** The probe checks this with `getSimpTheorems`. A new simp lemma could change the behaviour of
  existing downstream `simp` calls; a non-simp insertion cannot.

## 2. Deviations

- **D1. Three readers are not `rfl` (census said `rfl`).** `TreeCircuit.depth`, `size` and `maxFanin` are defined by
  well-founded recursion, so they are `@[irreducible]`.
  - A probe on the snapshot showed `rfl` failing on all three (`#print` shows `⋯.fix`; log in `probe/`).
  - They are proved by `simp [TreeCircuit.depth]` (and likewise for `size` and `maxFanin`), through the definitions'
    own equation lemmas `depth.eq_1` and so on. The owner unfolds its own definition, which is the form of the sibling
    reader `TreeCircuit.eval_lit`.
  - All three use the standard axioms, as `depth_node` does. The PR title keeps "pure rfl insertions" as given; the
    body discloses this deviation.
- **D2. Docstrings over two lines.** Five docstrings (`carryBit_succ`, `gatesAcyclic_iff`, `isWellFormed_iff`,
  `isPolySize_iff`, `hasPolylogDepth_iff`) take two lines, and `gadgetCorrect_iff` and `inTreeNC_iff` take three. The
  reason is that the formula and "Glue." do not fit in 100 columns. No added line is longer than 100 characters.
- **D3. First commit attempt.** The first signed commit, `faef08bd…` (never pushed), wrote `carryBit_succ` as
  `… = (A i && B i) || (…)`. That parses as `(… = (A i && B i)) || …`, and `Adder` failed with 2 errors
  (`build-attempt1-failed/`, kept). The right-hand side was parenthesised and the commit amended, still signed. All
  checks below are on the amended head.
- **D4. Full downstream replay deferred** (§4).

## 3. Pure insertion

- `git diff 8c5875fa 3ea428fd` has **0 removed lines** (`diff/pr.diff`, `diff/diffstat.txt`).
- `scripts/pureins.py`: for each of the 5 files, deleting the inserted lines (located from the `-U0` hunk positions)
  from the head blob gives the base blob byte for byte. The SHA-256 is equal in **5/5** files: **RESULT OK**
  (`diff/pure-insertion.txt`).
- `touched.py` base → head (`rule10/touched-head.tsv`) reports 13 ADDED, 0 REMOVED, all others UNCHANGED, except
  `BoolCircuit.Lit.eval`, reported CHANGED.
  - That is a span artifact: the "Section 2" comment banner that followed `Lit.eval` now falls inside the span of the
    inserted `Lit.eval_eq`.
  - `Lit.eval`'s own lines are unchanged.
- **Signature** (`git/signatures.txt`): the head carries an SSHSIG (ed25519, namespace `git`) with key
  `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`. This is the key of the tip and of #358.
  - Checked: only the key fingerprint, extracted from the blob. No `ssh-keygen` is installed on this host, so the
    signature itself was not cryptographically verified.
  - The trailers are exactly the two required lines.

## 4. Lean checks (snapshot #5 procedure; no `lake build`, no cache get)

- **Snapshot #5** `olean-snapshot` (T `3f540c22`, map `fca1b6a3…1ef9`): `snapmap.py verify` gives **1458 files, 0
  extra / 0 changed / 0 missing, RESULT OK** at three points: the start, after the build and seals, and the end. The
  tip `8c5875fa` is Lean-equal to T (`git diff` over `*.lean`, the lake files, `scripts` and `audits` is empty).
- **Downstream:** `downorder.py` gives changed 5 and **down 566**. `fullorder.py` gives 1427, and `stateplan plan`
  gives build 551 / reuse 876; the other 15 downstream modules are outside the root/Checks closure.
  - 566 is far above the ~150 limit, so the full downstream replay was **not run** (deferred to the next job that needs
    the downstream, e.g. the 6a fills' replay).
  - The deferral is safe: the insertions are non-`@[simp]` declarations under 13 new names with 0 clashes (§6), so they
    can affect a downstream module only by a name clash. The cross-builds below also exercise the merged `TreeNCAC`.
- **Sub-replay** in `$SP/olean-replay-6a-readers` (a `cp -al` of the snapshot):
  - It rebuilt the owners' import closure intersected with the downstream set, in order: `Basic`, `DAGCircuit`,
    `Adder`, `TreeDAG`, `DAGTransform`, `TreeNCAC`.
  - `TreeDAG` is not an owner. It lies between `Basic`/`DAGCircuit` and `DAGTransform`, so it was rebuilt so that every
    owner's whole upstream is either unchanged or rebuilt. The 7th closure module, `SpaceComplexity/Machines/Bin`, is
    unchanged and reused.
  - Results: **6/6 rc 0**, 0 `error:`/`error(`, 0 warnings, 0 `sorry` (`build/results.jsonl`, `build/mods/`).
  - All 6 rebuilt oleans have **link count 1** (`replay/rebuilt.tsv`). `TreeDAG`'s rebuilt olean is byte-identical
    to the snapshot's, so its content does not depend on the inserted readers.
  - No Mathlib overlay or NthRootLemmas was added: the owners' closure does not need them. A later full replay adds them
    per `snapshots.md` step 2.
- **State** (`replay/`):
  - `stateplan init` at `3f540c22` covers 1427 modules; `update` took 6.
  - `check` over the owners' 7-module closure gives **RESULT OK**.
  - `check` over the full closure gives RESULT FAIL with exactly 545 BAD, which equal the plan queue minus the 6
    rebuilt, i.e. the deferred downstream.
  - `replay/state.json` is the checked state for a later job that completes the replay.
- **Slots:** each Lean process waited (30 s polls) while `pgrep -c -x lean` was 3 or more (`scripts/slotrun.sh`,
  `scripts/runner_full_slots.py`; `*/slots.log`). This job ran one process at a time; up to 2 other jobs' processes
  were seen and the machine never exceeded 3.
- **Axioms** (`axioms/ReadersAxioms.log`; probe on the replay; rc 0, 0 errors):
  - **No axioms:** `Lit.eval_eq`, `carryBit_zero`, `carryBit_succ`, `gatesAcyclic_iff`, `isWellFormed_iff`,
    `gadgetCorrect_iff`.
  - `[propext, Classical.choice, Quot.sound]`: the 3 literal readers (equation lemmas of well-founded definitions) and
    the 4 `TreeNCAC` readers.
  - The `TreeNCAC` readers take these axioms from the constants in their statements: `IsPolySize`, `HasFaninTwo`,
    `HasPolylogDepth`, `Language.InTreeNC` and `TreeCircuit.depth` each print the same three.
  - Nothing non-standard appears. The probe also prints all 13 statements (`#check`) and `simp=false` for each.
- **Rule 10, canonical coe-A whole-file seals** (`rule10/`; the Gate 44/48 harness `g6a-p2/tools/seal`, unchanged,
  `SEAL_CHUNK=1000`):
  - Each of the 5 owners was sealed twice: at base (`wt-base` on the snapshot, read only) and at head (the replay).

    | Owner | Requests | Errors (base / head) | Failing declarations (base = head) |
    |---|---|---|---|
    | `Basic` | 0 / 0 | 0 / 0 | none (no foreign TCSlib definition in its closure) |
    | `DAGCircuit` | 0 / 0 | 0 / 0 | none (as above) |
    | `Adder` | 58 / 58 | 3 / 3 | `adderCircuit`, `adderCircuit_isFaninTwo`, `bitsVal_eq_logProg_bitsVal` |
    | `DAGTransform` | 174 / 174 | 11 / 11 | `DAGCircuit.rewrite`, `rewrite_eval`, `rewrite_depth_le`, `rewrite_length_le`, `rewrite_new_gates`, `rewriteGates_inv`, `rewriteInv_step` |
    | `TreeNCAC` | 94 / 94 | 4 / 4 | `maxDepth_map_le`, `maxFaninL_map_le` (G6A-F05), `maxFaninL_pairUp`, `sumSize_pairUp` |

  - Request rows, term names, exclusions and closure-module counts are **equal at base and head**. Stored constants
    grow by exactly the 13 readers (+4, +2, +2, +1, +4). All 10 runs have their install and EOF records.
  - With line positions stripped, all 5 seal logs are **identical at base and head** (`rule10/seal-base-vs-head.txt`).
    No failure is in a new reader, and the pre-existing failures are unchanged.
  - On G6A-F05: at the tip, `TreeNCAC` has 4 failures, not 2. O1 (#358) moves `maxFaninL_pairUp`/`sumSize_pairUp` to
    `Combinators` and repairs them, which leaves the 2 that G6A-F05 records.
  - Not run: strict A/B, coe-B, and the paired controls. This PR adds no definitions, so the coe-A run with base/head
    equality is the check that matters; the harness and its controls are the ones Gate 44/48 accepted.
- **Cross-builds of the merges** (`crossbuild/`):
  - Both `merge-tree` results with #358 (`fbed5136`) and #359 (`7d551d6f`) touch `TreeNCAC.lean`, and the merged
    `TreeNCAC.lean` is byte-identical in the two (`1df08c36…`).
  - Each merge's `FormulaArith/Combinators.lean` and `TreeNCAC.lean` were exported (`git archive`) and built on a
    throwaway `cp -al` copy of the replay.
  - Results: **rc 0, 0 errors** for all 4 modules; the only warnings are #359's 24 `sorry` warnings in its own
    `Combinators`.
  - The copy and the exports were deleted.

## 5. Lint (`lint/`)

- `campaign_style_lint.py TCSlib/Complexity --check8b`, base (records checkout) and head (worktree):
  - Both give **25 FAIL / 390 WARN** over 500 files, and the FAIL lines are identical.
  - Four check-8 WARN lines shrink:

    | File | Names | Removed from the list |
    |---|---|---|
    | `Adder` | 8 → 7 | `carryBit` |
    | `DAGCircuit` | 9 → 7 | both `IsWellFormed` entries (the lint matches by name) |
    | `DAGTransform` | 2 → 1 | `GadgetCorrect` |
    | `TreeNCAC` | 7 → 4 | `HasFaninTwo`, `HasPolylogDepth`, `IsPolySize` |

  - Otherwise only line-count INFO lines change. No new FAIL or WARN.
- `style_lint.py` on the 5 changed files gives **0 findings** at both base and head.
- `Basic.lean` is now 714 lines (698 before) and `DAGCircuit.lean` 742 (730), both above the 600 target as before. All
  5 files are under 1000.

## 6. Name clashes (`clash/clash-base-and-heads.txt`)

- `scripts/clash.py` indexes every keyword-line declaration in `TCSlib/` and `audits/`, private included, with
  namespace tracking.
- Revisions scanned: the tip, #358 `a616adca`, #359 `73aedcda`, #357 `7a98ba01`, #347 `daa6e173` and #355 `d3c7cb00`.
- **EXACT 0** at every revision.
- Same-last-component declarations, in other namespaces only:
  - `BoolCircuit.DAGGate.eval_eq`, `BoolCircuit.DAGCircuit.eval_eq`, and the GSW `eval_eq`;
  - `BranchingProgram.Instr.eval_eq` (#359).

## 7. Merge-tree (`merge/merge-tree.txt`; `git merge-tree --write-tree 3ea428fd <other>`)

| PR | Head | Result | Merged tree | Shared paths |
|---|---|---|---|---|
| #358 | `a616adcac0760ab56b1b0a2a4869f4763843f9ab` | clean | `fbed5136` | `TreeNCAC.lean` |
| #359 | `73aedcdaaaffef7e69ab012d9b9195f150bae68d` | clean | `7d551d6f` | `TreeNCAC.lean` |
| #357 | `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff` | clean | `33141074` | none |
| #347 | `daa6e173cdd94cad1475b9a96eca613bce53ba61` | clean | `5d8d9df6` | none |
| #355 | `d3c7cb00092ad5913904654d922f30fc7d5fce4a` | clean | `3fc95018` | none |

- In the `TreeNCAC` merges, this PR's hunks (lines 113–156 of the base) and O1's (from line 172, plus the import at
  line 10) are disjoint.
- Each merged tree keeps every line of the other head in this PR's 5 paths (0 removed lines against it).

## 8. Delivery and state at the end

- **Pushed:** `land/gsw-6a-readers` = `3ea428fd`.
- **PR #360:** draft, base `cryptography/pass-shelat-ch2-4`. GitHub rewrote the body's ending on creation; it was
  reset once with `update_pull_request`, and the stored body now equals `pr-body.md` byte for byte.
- **Kept:** `$SP/olean-replay-6a-readers`: snapshot #5's 1458 oleans, 6 of them rebuilt (link count 1), with no overlay.
  - Its state (`replay/state.json`) is OK over the owners' closure.
  - **545 downstream modules are stale.** A later job must replay them (plan queue `replay/plan/queue.txt` minus the
    6) before adopting or building on this tree.
- **Removed:** both sparse worktrees (`g6a-readers/wt`, `wt-base`), the cross-build copy and the exports. Scratch,
  scripts and evidence remain under `$SP/g6a-readers/`.
- **Disk:** 2672 MB free after the copy; 2682 MB at the end (other jobs writing).
- **Not touched:** other agents' directories, the snapshot (read and hard-linked only), Arora–Barak and Ladner
  material. The untracked `briefs/lattice-gsw/gates/45-gsw-6a/` in the records checkout is not this job's.
