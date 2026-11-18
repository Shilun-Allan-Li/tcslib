# GSW 6b U12 `gsw-6b-u12` · final r1 · maintainer review (phase 1 static, phase 2 Lean replay)

**Verdict after phase 2: ACCEPT. No landing edit.** The three targets G1–G3 of
`GSW/Branching.lean` are proved as stated. Phase 2 passed with no new finding. The details are in
[`phase2.md`](phase2.md).

- **Findings:** 0 blockers, 0 majors, 1 minor, 3 info.
  - The minor is **on our side**, not the worker's: U12-F01, `rulings.md` was never filed in the
    issued folder (shared with U13-F01).
  - The infos:
    - U12-F02: the dup-sweep's G1 hint cannot reach the frozen bound, and the worker's route is
      the right one.
    - U12-F03: `sigma1 0 ≠ 0` is proved by kernel `decide` through the reader; an optional
      promotion request.
    - U12-F04: housekeeping on the worker's own host.
- **Phase 2 (2026-11-18, 22:28–22:42 UTC; one replay tree, U12 and U13 stacked).**
  - **Build:** 12/12 modules rc 0, including the root `TCSlib`, with 0 errors. No `audits/*/Checks`
    imports the changed modules. U12 **alone** also passes: 11/11 rc 0, admissions 39 in 15.
  - **Axioms:** standard only. The census covers all 13 stored constants of `Branching`, with 0
    `sorryAx`.
  - **Seals:** canonical coe-A and seal B both give 0 errors, with 200 requests verified.
  - **Controls:** 2 liveness pairs, ALL_OK.
  - **Unfold scan:** 0 foreign definitions.
  - **Lint:** unchanged.
  - **Snapshot #11:** rehashes 0/0/0 before, after and at the end.

## What was reviewed

- **Delivery.** `inbox/fills/gsw-6b-u12/` on `exchange/pass-shelat-ch5-8`, at
  `9b4ab065f58581ac93ba6641f29a0d4051482dfa` ("fill gsw-6b-u12: final"). This was also the origin
  tip when I read it.
  - The commit is unsigned (0 `gpgsig`). Its parent is `87012e78` (U13's final), and it touches
    only `inbox/fills/gsw-6b-u12/`. The checkpoint `f190df17` also touched only that folder.
  - Extracted with `git archive`, the delivery has 410 files: `REPORT.md`, 2 patches with
    `COMMITS.tsv`, `src/` (1 file) and `evidence/` (404 files).
- **Contract.**
  - The issued pack at the records pin `bbc930b3853adb29ba96324568e984d521abd257`: `README.md`,
    `COMMON.md`, `U12/brief.md`, `U12/dispatch-prompt.md`, `dup-sweep.md` (§0, §U12),
    `targets.txt` and `base-sorries.txt`.
  - Since the pin, only `U12/dispatch-prompt.md` and `U13/dispatch-prompt.md` changed (the pin
    hash was filled in, 4 lines each); the brief, `COMMON.md` and `dup-sweep.md` are unchanged.
  - Handoff §2: rules 10 and 15, and the duplication rule; `policy.md` §1–§3.
- **Rulings in force.** Gate 46 (CLEAR) and the 6b rulings Q-6B-W1–W3, F1, F2, Q-6B-1 and Q-C1. None
  of them bears on Branching's proofs. The folder's own questions Q-6BF-1..7 are unruled (U12-F01).
- **Base.** B6 = `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`, tree `845bdc98…`, checked with
  `git rev-parse`.
  - The records tip `31247fe71e7ab60a1d7f8f1939291147e1b5645a` is Lean-equal to B6: the
    `git diff --name-only` over `TCSlib`, `TCSlib.lean`, `audits`, the lake files and
    `lean-toolchain` is empty.
- **Precedent for format and method:** `EF-H12/final-r1/`.
- **Tools.**
  - Phase 1 used `git` and `python3 -I` only.
  - Scratch work is under
    `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g6b-u1213/`.
  - Nothing was committed or pushed. The main checkout was only read, apart from this folder.

## Checks

| Check | Result |
|---|---|
| **Integrity** | **PASS.**<br>• Both manifests pass `sha256sum -c`: 409 top-level rows and 403 evidence rows.<br>• No duplicates, no leading `./`, and neither manifest lists itself.<br>• Each manifest equals its tree exactly.<br>• The top level binds `evidence/SHA256SUMS` (unlike EF-H12-F05d). |
| **Reproduction (C13)** | **PASS: 2/2 hashes reproduced.**<br>• `git am` on B6 in a scratch sparse worktree, unsigned, with committer data from `COMMITS.tsv`, gives `f0a51d1ed18253596aba2bf2f8450c8f93b186bf` and then **`afdaa9e2f29604052537652bf01165e61c52fb32`**, REPORT's head.<br>• 0 `gpgsig`.<br>• `src/…/Branching.lean` equals the head byte for byte.<br>• Checkpoint 1 delivered the same head: `src/` and `patches/` are unchanged between `f190df17` and `9b4ab065`. |
| **Scope** | **PASS.**<br>• `git diff --stat bff0567b afdaa9e2` shows only `GSW/Branching.lean`, +102/−13.<br>• Each of the two commits touches only that file. Commit 2 is a one-line docstring fix to the glue's formula.<br>• `git merge-tree --write-tree` with the records tip is clean (tree `f8ef0779…`). |
| **Statements (C3), independently** | **PASS.**<br>• decls2 (records copy `fa81981a…`) at the head against B6: **0 ADDED, 0 CHANGED, 0 REMOVED**.<br>• Live control: making the glue public gives 1 ADDED.<br>• **Headers compared exactly** (my `frozen.py`): G1, G2 and G3 have headers (4, 6 and 6 lines, keyword through `:= by`) and statement prose before `**Proof sketch.**` byte-identical to B6. |
| **Frozen regions (C4), independently** | **PASS.**<br>• The head normalizes **byte-identically** to B6 after four steps: each target's body is set back to `sorry`, the three refreshed sketch regions are set back to B6's, the one new `private` declaration (13 lines) is deleted, and the module sentence "All three are proved here" is set back to "statement-phase targets (admitted)".<br>• So no definition, reader, `set_option`, import, namespace or other text changed.<br>• Controls each FAIL: a one-character header change, a definition-body change (`select`) and a statement-prose change. |
| **Public declarations** | **PASS.** The brief allows none, and none was added. The only new name is `private theorem encrypts_select_ite`. |
| **Admissions** | **PASS.**<br>• 0 `sorry`, `admit`, `native_decide`, `axiom` or `opaque` in the code (comments stripped).<br>• No new `set_option`, `attribute` or `@[simp]`.<br>• Base→head: 3 `sorry` → 0. |
| **Axioms (C5)** | The worker gives 13 constants, all standard, `SORRY-REACHING 0`. **Phase 2 reproduces this independently:** the same 13 constants with the same sets, the targets each `[propext, Classical.choice, Quot.sound]`, and the `sorry` control flagged. |
| **Rule 10 (C6)** | The worker ran whole-file seals strict-A/B and coe-A/B at the head and the base: all rc 0, 0 errors, 200 requests; plus a liveness pair on `evalWith`. **Phase 2:** canonical coe-A and seal B both give 0 errors with 200 requested and 200 verified, my own 2 liveness pairs are ALL_OK, and the explicit-unfold scan finds 0 foreign definitions. |
| **Duplication** | **PASS:** no restatement, no inline re-derivation, no cross-file copy (below). |
| **Hygiene (C8, C9)** | **PASS.**<br>• 179 → 268 lines (+89, under the 150–250 estimate and the 450 cap); maximum width 97; no micro sign.<br>• All three targets keep sketches, refreshed to the delivered proof with prose untouched. G2's 42-line body has step comments at each `have`.<br>• The glue has a docstring with its formula and "Glue: …". |
| **Lint (C7)** | **PASS.** `campaign_style_lint --check8b` gives 92 FAIL / 103 WARN over 540 files at B6, at `afdaa9e2` and at the stack. The line sets are identical. `style_lint` gives 0 findings. |
| **Clashes (C10)** | **PASS.** `encrypts_select_ite` occurs in no `TCSlib/` or `audits/` file of any of the **336** local heads (`git grep -w`). It is private, so no resolution can change. |
| **Build (C1)** | The worker reports 224 bootstrapped modules, rc 0, the base census 42 in 16, and a head sweep of 10/10. **Phase 2:** 12/12 rc 0 in the stack (with root `TCSlib`) and 11/11 alone. |

## The proofs, target by target

- **G1 `Encrypts.select`.**
  - **Route.** `select_eq`. `Encrypts.sub` with `encrypts_gadget` gives `G − C ↦ 1 − b` with noise
    `0 + β`. Then case on `hb`:
    - the product whose left operand encrypts `1` uses `Encrypts.mul_bit` at `true`, with noise
      `N·β + βV`;
    - the product whose left operand encrypts `0` uses `Encrypts.mul`, with noise
      `N·β + |0|·βV`.
  - **Closing.** `Encrypts.add`, then `Encrypts.mono` by `simp; omega`.
  - **Correct and minimal.** `Encrypts.mul_bit`'s noise is `N·β₁ + β₂` whatever the bit
    (`Noise.lean:247`). Using it on both products would give `2·βV + 2·(N·β)`, which is above the
    frozen `βV + 2·(N·β)` (U12-F02).
  - **No `|1 − b| + |b| = 1` lemma is stated**, as the brief asked.
- **G2 `encrypts_homEvalPBP`.**
  - **Route.** The host `BranchingProgram.evalWith_rel` (C7) relates the homomorphic run to the
    Boolean run `if b then v else u` on `Pi.single s₀ 1`. The relation is "coordinate `i`
    encrypts with noise `τ·(2·(N·β))`".
    - **Step 0:** `encrypts_gadget` and `encrypts_zero` through `Pi.single_eq_same` and
      `Pi.single_eq_of_ne`.
    - **Step `τ`:** the instruction is a permutation, by the two readers
      `BranchingProgram.isPermutation_iff` and `Instr.isPermutation_iff`, never by unfolding.
      Both runs are rewritten to the pull form (`Instr.stepWith_of_isPermutation`, C6). The
      private glue then gives `τ·X + X`, and `ring` closes.
    - **End:** `evalWith_single` (C8), and a two-case reading of `Pi.single _ 1 i` as
      `(decide _).toNat`.
  - The host induction is not re-proved.
- **G3 `encrypts_homEvalFormula`.**
  - **Route.** `homEvalFormula_eq`, then G2 for `barrington c sigma1` (`isPermutation_barrington`)
    at `s₀ = 0`, `i = sigma1 0`.
  - **The message:** `barrington_yield_zero hc isFiveCycle_sigma1 x` and cases on `c.eval x`.
  - **`sigma1 0 ≠ 0`:** `rw [sigma1_eq]; decide`, which is kernel `decide` on Mathlib's
    `List.formPerm` over `Fin 5` (U12-F03).
  - **The noise:** `barrington_length_le` and `Encrypts.mono`.
- **The glue `encrypts_select_ite`** (private, 13 lines with its docstring) is G1 at `b.toNat`, read
  as the Boolean branch: `cases b <;> simpa`.
  - It is a disclosed specialization inside the same file, used only by G2.
  - It re-proves nothing.

## Duplication sweep (binding)

- **`dup-sweep.md` §U12 must-reuse list.** Every item is used, or has a reason I accept:
  - **Used:** `Encrypts.mul`, `.mul_bit`, `.add`, `.sub`, `.mono`, `encrypts_gadget`,
    `encrypts_zero`, the three own readers, `evalWith_rel`, `evalWith_single`,
    `Instr.stepWith_of_isPermutation`, `isPermutation_iff` (`Defs.lean:323`),
    `Instr.isPermutation_iff`, `isPermutation_barrington`, `barrington_yield_zero`,
    `barrington_length_le` and `isFiveCycle_sigma1`.
  - **Not needed:**
    - `mul_eq` (`select_eq` exposes `mul`, and the closure lemmas take it as is);
    - `encrypts_iff` (no error vector is opened);
    - the family `isPermutation_iff` (`:450`);
    - `isFiveCycle_iff` (the brief's `decide` alternative was taken).
- **My searches** (Mathlib at the pinned package, TCSlib at B6, and `exact?` probes on the
  replay tree):
  - **D1, G2's `hm`:** `((Pi.single a 1 i : ℕ) : ℤ) = (decide (a = i)).toNat`. `exact?` finds
    nothing, and a grep of Mathlib for `Pi.single … toNat` and `toNat_decide` finds nothing. It is
    a two-case use of `Pi.single_eq_same`/`_of_ne` and `decide_eq_true`/`_false`.
  - **D2, G2's `hι`:** "an instruction of a permutation program is a permutation instruction".
    `exact?` offers only `hB ι h`, a defeq read of the foreign `IsPermutation`. The worker's
    reader composition is the correct form, and no public lemma states it (the `Defs.lean`
    `IsPermutation.*` lemmas are `append`, `conj`, `complementLast` and `bijective_yield`).
  - **`sigma1 0 ≠ 0`:** the general fact is the **private** `IsFiveCycle.apply_ne`
    (`Barrington.lean:384`). It is not copied.
- **Near relatives, as disclosed:**
  - `Encrypts.nand` and `Encrypts.mul_le` are bit-gate analogues, not selectors;
  - `encrypts_chain` is the additive chain;
  - `Eval.lean`'s private `stepWith_single` is used through C8.

  None is restated.

## Findings

**Blockers: none. Majors: none.**

- **U12-F01 (minor; records side, no change to the delivery). The pack's `rulings.md` was never
  filed.**
  - **What the pack says.** The pack expected the file at its pin:
    - README *Blocking* 1: "`<RECORDS>` … is the hash of the commit that files its final form
      with `rulings.md`";
    - README *Maintainer steps* 1: "Record Seyoon's answers in `rulings.md` in this folder (even
      'all as recommended')";
    - `COMMON.md`'s preamble: "Seyoon's rulings … (recorded beside it at the records pin) win
      over both";
    - all five dispatch prompts: step 1, "read … `issued-6b-fills-r1/rulings.md` … first".
  - **What happened.** The pin `bbc930b3` ("pin for U12, U13") does not contain the file, and
    no commit on any ref ever added it (`git log --all` on the path is empty). Decision-log row
    607 shows the choice: "U12 and U13 need no ruling and are pinned now; Q-6BF-1..7 for the
    morning". The prompts were not adjusted to match. No Q-6BF ruling is recorded anywhere
    since.
  - **Impact on U12: none.**
    - README *Blocking* 2 says "U12, U13 depend on none of the questions", and I agree:
      - Q-6BF-1 and Q-6BF-4..7 are EF-R1's;
      - Q-6BF-3's helpers are U14-U16's and U18-U19's (U12's brief allows none, and none was
        added);
      - Q-6BF-2's grouping gives U12 the same file and targets under A and B. Under C, U12
        would be a sub-agent of one job, but Seyoon dispatched U12 on its own (row 608).
    - The worker read every input at the pin with matching hashes, and reported the gap at
      once (U12-W1).
  - **Fix.** Records only:
    - answer Q-U12-1;
    - file `rulings.md` (or a decision-log row) saying that no Q-6BF ruling applies to U12/U13;
    - record Q-6BF-1..7 before U14–U19 or EF-R1 are dispatched. Those prompts name the same
      file, and their units do depend on Q-6BF-2/3.
- **U12-F02 (info; pack defect, worker correct). `dup-sweep.md` §U12's G1 hint is wrong.**
  - **The hint.** The sweep says "apply `Encrypts.mul_bit` with `b.toNat` for the two products
    rather than re-deriving `|1 − b|·βV + |b|·βV = βV`". The brief's first alternative says the
    same.
  - **Why it fails.** `mul_bit` charges `β₂ = βV` on the `0`-message product too, giving
    `2·βV + 2·(N·β)`, which is over the frozen bound.
  - **What the worker did.** The brief's second alternative (`Encrypts.mul`, whose `|0|·βV`
    vanishes), on that product only. This is the minimal correct route, and it re-derives no
    general identity. It is disclosed (U12-W2).
  - **Fix.** None to the delivery. Q-U12-2 records it.
- **U12-F03 (info). `sigma1 0 ≠ 0` by kernel `decide` after the published reader `sigma1_eq`.**
  - **Rule 10.** `List.formPerm` and `Fin 5` are Mathlib/core, which may reduce in a `decide`
    step (COMMON §5.1). The seals confirm that no TCSlib definition is read: `sigma1` stays sealed.
  - **The alternative.** The general fact is private in `Barrington.lean`. The worker's optional
    promotion request (a public `IsFiveCycle.apply_ne`) is reasonable but not needed (Q-U12-3).
- **U12-F04 (info). Host housekeeping on the worker's side.**
  - To pass its 12 GiB disk preflight, the worker deleted two of its own finished worktrees on
    its host (`/workspace/scc`, branch ref kept; `/workspace/scbase`).
  - It touched nothing of ours and changes nothing here. Recorded for completeness.

## Questions for Seyoon (recommended option first)

- **Q-U12-1 · the missing `rulings.md` (U12-W1; the same as Q-U13-1).**
  - **A (rec.)** Confirm that no ruling applies to U12 (or U13) and accept the deliveries as
    they are. Record it in the decision log, and file `issued-6b-fills-r1/rulings.md` with the
    Q-6BF-1..7 answers before any further unit of the folder is dispatched.
  - **B** File `rulings.md` first and have both deliveries re-checked against it. Not needed:
    no question bears on U12/U13.
- **Q-U12-2 · G1's route (U12-W2).**
  - **A (rec.)** Accept it as delivered: `mul_bit` on the `1`-bit product and `Encrypts.mul` on
    the `0`-message product. The sweep's hint is noted here as wrong (U12-F02). The issued pack
    stays as pinned.
  - **B** Also correct `dup-sweep.md` §U12 in place. Not recommended: issued packs are pinned
    records, and this review carries the correction.
- **Q-U12-3 · promotion request: a public `IsFiveCycle.apply_ne` in `Barrington.lean`.**
  - **A (rec.)** Decline for now. G3 does not need it, and it would be an owner edit to a 6a file
    for no current consumer. Revisit if a second consumer appears.
  - **B** Queue it as a one-declaration owner PR (remove `private`, add a docstring formula).

## Landing

- **Landing.** One PR with the two worker commits, as delivered (no landing edit). The README
  orders U12 first, then U13.
  - The two files are disjoint and neither imports the other. The stack is Lean-tested
    (`fb6884d1`), and so is each unit alone.
- **The prospective trees:**
  - U12 alone on the records tip: `f8ef0779…`;
  - U12 + U13: `fb6884d1…`.
- **Snapshot.** The replay tree was deleted. Rebuilding it takes about a minute (12 modules, about
  25 s of Lean). Snapshot #12 can be adopted from a fresh replay of whatever merges.

## Evidence

`gsw-6b-u12-u13-final-r1-evidence.zip` sits beside this file; its SHA-256 is in
`evidence-SHA256SUMS`. The same zip is filed under `U13/final-r1/`.

- It holds `PROVENANCE.txt` and an inner `SHA256SUMS` (271 files), which does not list itself.
- It contains the integrity and reproduction logs, the frozen check with its controls, decls2,
  the static scans, and the stack and alone replays.
- It also contains the axiom census, the collector, the coe-A and seal-B records with their
  sealed copies and raw logs, the controls, the duplication probes, the unfold scan, lint, and
  every tool and probe source.
