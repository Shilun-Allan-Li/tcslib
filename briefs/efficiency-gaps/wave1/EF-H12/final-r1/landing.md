# EF-H12 `ef-h12-levin-3col` · final r1 · landing

**Landing branch pushed: `land/ef-h12-levin-3col` at `11f33ef370efe39dc62c958b99836df0d874b18f`.**

- **Base:** `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`, the base of phase 2's check head.
- **Commits:** the 19 worker commits and four signed maintainer commits: LE-h12-arith, LE-h12-strip,
  LE-h12-bridge and LE-h12-doc.
- **Rulings applied** (decision-log rows of 2026-11-18/19):
  - EF-H12-R1 (A), under EF-W1-R (A): LE-h12-bridge. The bridge keeps its 27 readers.
  - R2 (B): nothing in this branch. The course file gets its own owner PR later; the bridge keeps
    its course section until then.
  - R3 (B): LE-h12-arith. It supersedes LE-h12-pow.
  - R4 (A): the [AB09] ch. 2/6, [GJS74] and [St73] ingests are done; LE-h12-doc applies their
    dispositions.
  - R5 (A): `polyTimeComputable_foldl_accept` stays as a registered host (ledger DL-64/DL-65,
    already filed). No code change.
  - "Course-file attribution ruled": the course file's [St73] References line belongs to the R2 (B)
    owner PR, so it is not in this branch.
- **LE-h12-priv (I2) was not done.** The review does not mark it safe, and it is not: the conditional
  form `polyTimeComputable_colorInst_of` is declared in `ColoringGraph.lean` and used in
  `ColoringParse.lean:718`. A `private` mark would break that use.
- **No PR is open.** Seyoon opens it as a draft; the body below is ready to use.

Run on 2026-11-19, 05:25–07:20 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`, and the work is in
`$SP/land-efh12/`.

## Inputs

- **Delivery.** `inbox/fills/ef-h12-levin-3col/` at exchange commit `36d9ac03c329544d33b1f3f9a73e6ce32152dde2`.
  - Its tree is `4d55bc05…`, the same as at the exchange tip `8f15c31d`.
  - The extraction in `$SP/efh12/delivery` equals a fresh `git archive` of that commit (`diff -r` empty,
    1,685 files).
  - The top `SHA256SUMS` (`92e5405e…`) and `evidence/SHA256SUMS` (`5f53bf27…`) both verify, with 0
    failures. These are the hashes phase 1 recorded.
- **Records tip.**
  - The job started at `ddd1a386`.
  - The re-check merged `fb57a36c`, which adds the records-only commit "records: EF-H12 landing
    started".
  - Against `bff0567b`, its Lean differs only in `GSW/Branching` and `GSW/DecryptFormula` (U12/U13,
    #392).
- **Replay tree.** Phase 2's `$SP/olean-replay-efh12` was state-checked before it was copied: 1469/1469
  RESULT OK at `63d619e8`.
- **Snapshot #11.** `snapmap verify` gave 0/0/0, RESULT OK, with map `e7bb03b4…867d0`.

## Commits

| # | Landing commit | Worker commit | Subject |
|---|---|---|---|
| 1 | `9ce998914f51b34e791b0dc9f2be13ef60e25633` | `b9a365ef` | LevinHardness: the witness relations R_CKT and R_3SAT |
| 2 | `ccc04f8daa55053b1c68c9a91de66df60994a770` | `97c21391` | LevinHardness: the 3SAT-to-3COL gadget graph laid out on Fin N |
| 3 | `f6b160b308e8ce9571c1508ff4420b5910787c11` | `8e8038bb` | LevinHardness: step 1, certificate, verifier and tableau instance map |
| 4 | `95df3272d2038d5ce3e45ec3320533e2242b2502` | `3fdbc34f` | LevinHardness: quarantined reader bridge for frozen definitions without readers |
| 5 | `b5e78ce42b9b415698c42a8ba3a7a482b66f271f` | `0958b188` | LevinHardness: step 2, wire-value witness along the Tseitin map |
| 6 | `b6516994a71035f4e15c1c60406ac4a0a13d1aea` | `5ab2b55a` | LevinHardness: step 4, explicit 3-colouring witness, re-derived and disclosed |
| 7 | `5eaa6b5e97393073064581995e6a47179c11c669` | `9f12ab83` | LevinHardness: bridge readers for the CNF serialization |
| 8 | `66c1df0f8b00c169ab390831f4353312a1169763` | `d2272e8e` | LevinHardness: step 3, gadget instance map and vertex equivalence |
| 9 | `30eac4ac5ba9b54cc08e77f74111c271d0e3dfaa` | `ac784b5b` | LevinHardness: soundness transported from the course reduction |
| 10 | `ea7113d14dd189ea2a3613d64abbbebc162f9af2` | `f77fad29` | LevinHardness: isolated-vertex padding of graphs and colourings |
| 11 | `55d3f1f5f78cfe4691889b2ff4ac1a6569fdf8fd` | `02df6dcd` | LevinHardness: CircuitWitness line width |
| 12 | `e85a22a9722e10ccc516d380466b2854ef6c6650` | `0c95b0b9` | LevinHardness: bridge reader for LevinNPHard; soundness exposes … |
| 13 | `b39a5597c0c26a8e718429599722f472b1ca2aa1` | `6a3e1259` | LevinHardness: public unary arithmetic rows; ColoringGraph uses them |
| 14 | `7c4cb29f2a45bd410f89d5c18e19e4d1fe187849` | `3a47faca` | LevinHardness: polynomial-time clause-membership and width tests |
| 15 | `dcdc5b12e6657a64aaba50928bd98a1a739b00a2` | `085ebe3b` | LevinHardness: ColoringWitness uses the public unary rows |
| 16 | `1c9492e15d8158b5f1783a75afbc49fe47a77191` | `3b0bdbcd` | LevinHardness: assembly, levinNPHard_L3COL and the unconditional ZK corollaries |
| 17 | `bf827aeaefbc888b43321e1d7e828a94be247b55` | `36ddbfee` | ZeroKnowledge: LevinHardness facade |
| 18 | `94376f6a0f9cb84df4553cd9310f8574e9e6fcdd` | `5dabd164` | LevinHardness: proof sketches and module-docstring sections (style lint) |
| 19 | `393c5cc1f1690114bb52cae031c3d71a24c6bf9c` | `c8d5b3c7` | LevinHardness: verTime_eq reader |
| 20 | `4230f872fff33da4e8ce4b47906b4a0df6774c36` | (maintainer) | LE-h12-arith: remove the restated UnaryArith rows (EF-H12-R3 (B)) |
| 21 | `76676c145a8004a2451d55654e79a61e31881ec7` | (maintainer) | LE-h12-strip: read the catalog's strip match through its equation lemmas (F08) |
| 22 | `ad07b07c4eeca3cda93312c04448b39925cd1669` | (maintainer) | LE-h12-bridge: record the bridge as the bounded exception of EF-H12-R1 (A) |
| 23 | `11f33ef370efe39dc62c958b99836df0d874b18f` | (maintainer) | LE-h12-doc: citation fixes from the [AB09] and [St73] ingests (F05c, F07) |

(Subjects 5–15 are shortened here; the commits carry the worker's full subjects.)

- **Commits 1–19** come from `git am -3 -S` of the 19 delivered patches on `bff0567b`.
  - **The tree after commit 19 is `efdd41d867a0d057d7fce00b915aedcc743138f3`**, phase 2's check-head tree
    (`63d619e8`) and phase 1's `merge-tree` prediction.
  - Author name, e-mail and date, the message, and the patch-id of every commit equal the worker's
    `c8d5b3c7` series. Both authors are kept: "Claude (EF-H12 fill)" for 1–3 and "Claude-EF-H12" for
    4–19. Each commit keeps the worker's own `Claude-Session` trailer (I4).
  - The 14 files are byte-identical to the delivered `src/`, with the same path set.
- **Commits 20–23** are staged by explicit path. Each message ends with exactly the two required trailer
  lines.
- **All 23 commits are SSH-signed**, with one `gpgsig` each.
- **Branch diff against the base:** 14 files, +4,068/−0. The tree is `07618377…`. Against the worker's
  head, the four landing edits are +167/−99 over 13 files.

## Landing edits

- **LE-h12-arith** (EFH12-F02; EF-H12-R3 (B); supersedes LE-h12-pow). +32/−45 in `UnaryArith.lean` and
  `ColoringGraph.lean`.
  - `unaryPow_poly`, `unaryDiv_poly` and `unaryMod_poly` are deleted.
  - Powers now come from `EncodingMachines.unaryPolyOf_poly (.pow .var k)`, read through
    `PolyExpr.eval_pow`/`eval_var`. This covers `clauseLit_poly` and the `gadgetN` bound in
    `polyTimeComputable_gadgetAdj` and `polyTimeComputable_colorInst_of`.
  - Quotient and remainder now come from `divNum_poly`/`modNum_poly` with `divNum_eq`/`modNum_eq`.
    This covers `unaryDivConst_poly`, `unaryModConst_poly`, `clauseLit_poly`, the gadget-edge test and
    the chunk of `colorInst_of`.
  - The gadget-edge test first turns `/` and `%` into `divNum`/`modNum` with
    `simp only [← divNum_eq, ← modNum_eq]`. `apply divNum_poly | apply modNum_poly` stand **before** the
    arithmetic alternatives of its `repeat' first`.
    - A first attempt listed them last. There, `apply unarySub_poly` closed `modNum` goals by
      unfolding `modNum` to `a − divNum a m · m`: a definitional read of a foreign definition. Lean's
      unused-tactic linter showed it: `apply modNum_poly` was never reached.
    - The final order compiles with 0 warnings. The canonical coe-A seal of `ColoringGraph` is 0
      (below).
  - The statements of the remaining declarations are unchanged. `ColoringGraph` now takes 30 s,
    against 12 s in phase 2.
- **LE-h12-strip** (EFH12-F08). +25/−2 in `Verifier.lean`; the statement is unchanged.
  - **The proof.** The proof transports `computesFunInTime_stripLast` along a pointwise equality
    (`cast (congrArg … (funext …))`):
    - `split` the catalog's outer `match` on `pairDecode z`;
    - `cases` on `splitAtLastTrue v`;
    - rewrite the inner `match` by the equation lemmas of its matcher,
      `Turing.FinTM.stripLastTM_computes.match_1.eq_1`/`eq_2`, as propositional steps
      (`refine (… .eq_N …).trans ?_`);
    - close the `stripCert` side by `simp only [stripCert_eq, …]`.

    A proof sketch is added.
  - **N4 check (new probe `N4Strip`).** The probe replaces the matcher by an **axiom** of the same type.
    Every TCSlib constant of the closure that mentions it is rebuilt over the axiom:
    - foreign theorems and the matcher's generated `eq_N`/`splitter` become axioms with the replaced
      statement;
    - definitions are re-added;
    - the module's own theorems are re-checked by the kernel.
  - **N4 result.**
    - The landing proof is accepted. Only `polyTimeComputable_stripCert` is re-checked; the axiomatized
      statements are `computesFunInTime_stripLast` and the matcher's `eq_1`/`eq_2`.
    - The delivered (F08) proof, compiled as a control, is rejected: kernel "application type
      mismatch".
  - **Deviation from phase 2's candidate.** Phase 2's candidate
    (`convert hM using 2; rw [stripCert_eq]; split <;> split <;> simp_all`) does not meet the N4
    boundary:
    - unsealed, `convert … using 2` closes the goal by defeq ("no goals" at `rw`);
    - with `convert` replaced, the `split <;> split <;> simp_all` and `repeat' split; simp_all`
      forms are both rejected by the N4 kernel check, because `simp` and `split` reduce the matcher
      at `some u` definitionally.

    The landing proof is the one that passes.
  - **Residual (information).** The catalog statement has a second, outer matcher: the **private**
    `Turing.FinTM.extract_run.match_1` of `Build/Primitives.lean`.
    - `split` reduces it at constructors definitionally.
    - No seal can name it from outside its file, and its equation lemmas cannot be named in source.
    - With both matchers axiomatized, the N4 probe rejects the landing proof as well.
    - This residual was already in the delivered proof, and the canonical seal does not cover it.
    - It is not the F08 finding, and repairing it needs an owner-side reader for the catalog
      function (a follow-up below).
- **LE-h12-bridge** (EFH12-F01; EF-H12-R1 (A)). Docstrings only, +45/−28 in three files. The 27 readers
  are unchanged.
  - **`Bridge.lean`.**
    - It cites the decision-log row "EF-H12-R1 ruled (A)" (2026-11-18, under EF-W1-R (A)) and ledger
      DL-65, instead of "user ruling".
    - It names all three owner groups, `ZeroKnowledge/NP.lean` included, and states that the file
      holds exactly these 27 readers.
    - It gives each group's repayment:
      - the 10 `Formulas/CNF`, `Formulas/CNFEncoding` and `DAGCircuitSat` readers by one owner PR;
      - `levinNPHard_iff` into `NP.lean` after #390;
      - the 16 course readers by the R2 (B) owner PR.
    - It states which readers are **case lemmas**: `syntaxStep_eq` and the nine `edgeRelation_*`,
      seven of which use `simp` with `EdgeRelation`'s equation lemmas. The other 17 are
      `rfl`/`Iff.rfl`. The table gains a proof column.
  - **`Soundness.lean:23` and `LevinHardness.lean:35`.** "user ruling" is replaced by the decision-log
    row.
- **LE-h12-doc** (EFH12-F05(c), F07, [St73] F1–F4 and F6). Docstrings only, +65/−24 in nine files.
  - **F05(c).** `CircuitWitness.lean` no longer says `R_3SAT_wireValues` takes the Tseitin equation as a
    hypothesis; it names `Bridge.toCNF_eq`.
  - **F07**, per `ingest-report.md`:
    - (a) `CircuitWitness.lean:310` cites [AB09, Def 6.1], not Def 6.9, and its References entry
      changes to match.
    - (b) `Relations.lean:23`: the default-`false` reading is marked as TCSlib's convention, and
      [AB09, Def 6.9] keeps `u ∈ {0,1}ⁿ`.
    - (c) "(§2.3.)" is dropped from the [AB09] entries of `Gadget`, `Padding` and `UnaryArith`, and so
      is `UnaryArith`'s in-text "[AB09, §2.3]".
    - The CUP numbers are kept, and "§2.3" stays on the four 3SAT → 3COL files.
  - **[St73]**, per `ingest-report-st73.md` "Final citation texts" and the maintainer's dispositions:
    - **F1**: `levinNPHard_L3COL`'s docstring, verbatim.
    - **F2**: the `Hardness` module text and References.
    - **F3**: the `LevinHardness` facade. It also gains the course entry.
    - **F4**: the `ZeroKnowledge` facade bullet and References.
    - **F6**: the positive attributions in `Gadget.lean` (the node map, the palette triangle and the
      extra base edge) and `ColoringWitness.lean` (the completeness colouring that [St73] leaves to the
      reader).
    - The six files gain the [St73] References entry: "(Theorem, p. 22; proof pp. 21–22; Fig. 1, p. 24.
      The printed pages of this issue are bound out of order: the proof of part 1), the reduction from
      3SAT, runs from p. 22 back to p. 21.)".
    - [GJS74] and [GJ79] do not appear in Lean (`grep` gives 0).
    - The optional F6 parts (`Soundness`, `ColoringGraph`, `ColoringParse`, `Bridge`) are not applied,
      since only Gadget and ColoringWitness were adopted.
    - **F5** is a `REPORT.md` text. `REPORT.md` is not in the branch, so F5 belongs to the records.
  - **The gate's five F-checks hold:**
    - (a) [St73] is cited only for Karp's statement and the reduction;
    - (b) the deviation note is in F1;
    - (c) nothing cites [St73] for the circuit route or the padding;
    - (d) there is no [GJS74];
    - (e) the Theorem is cited at p. 22.

## Re-check on the landing head

The re-check followed phase 2's recipe and the EF-H11 landing: the `snapshots.md` job recipe and the
tools of `olean-advance-a6d01b1b/tools-used/`, all with `python3 -I`. There was no `lake build` and no
cache get.

- **Scratch check head** (never pushed). A sparse detached worktree at `11f33ef3` was merged with the
  records tip `fb57a36c` (`--no-ff`, unsigned).
  - The result is `a3617cde18766131a63c5f0b766a073d4863f832`, tree `d55035ca…`.
  - That tree equals `git merge-tree --write-tree 11f33ef3 fb57a36c`.
- **Olean tree.** `cp -al $SP/olean-replay-efh12 $SP/land-efh12/replay`: 1,501 files, all hard links, and
  3,346 Mathlib symlinks.
- **Plan.**
  - `fullorder` gives 1469 modules, the same as phase 2. `stateplan plan` gives **27 to build and 1442
    reused**:
    - the 12 LevinHardness modules and the two facades;
    - U12/U13 and their GSW downstream (11 modules);
    - root `TCSlib`;
    - `audits/pass-shelat/Checks`.
  - `audits/garg-ch1-3/Checks` is reused.
  - The plan, build and update ran with the check head's **tree** id `d55035ca`, by an oversight in
    the order of the printed hashes. `stateplan` keys are source-content hashes, so the commit and its
    tree give identical keys. Re-run at the commit `a3617cde`: `fullorder` is identical, `plan` gives
    0 to build, and `check` gives 1469/1469 RESULT OK.
- **Build.**
  - **27/27 rc 0.** `error:` 0, `error(` 0, the substring "error" 0. `permod` found no log/record
    mismatch.
  - The only warnings are 15 `declaration uses 'sorry'`, in the six records-side GSW files: `Bootstrap`
    5, `PolyRatio` 3, `Asymptotic`, `Leveled` and `LeveledSecurity` 2 each, `Circular` 1. These match
    the `sorry` tokens of those files at the check head.
  - The 14 EF-H12 modules, root `TCSlib` and `Checks` have **0 `sorry` and 0 warnings**.
- **Accept.**
  - `stateplan update` took 27 modules, none left out.
  - `check` gave **1469/1469 RESULT OK**.
  - All 27 rebuilt oleans have link count 1.
- **Admissions.** The landing edits add 0 `sorry`, `admit`, `native_decide`, `axiom` or `opaque` tokens.
- **Axioms** (`AxiomsLand`, phase 2's census probe unchanged). It ran with rc 0, and its one warning is
  the control's.
  - **488 stored constants** in the 12 modules and the facade: 189
    `[Classical.choice, Quot.sound, propext]`, 134 `[Quot.sound, propext]`, 96 `[propext]` and 69 `[]`.
    None is non-standard.
  - **Against phase 2's 483:**
    - 3 are gone: `unaryDiv_poly`, `unaryMod_poly` and `unaryPow_poly`.
    - 8 auxiliaries are new: two `_simp` lemmas of `polyTimeComputable_gadgetAdj`, and in `Verifier`
      the private generated `eq_1`/`eq_2`/`splitter` of the two catalog matchers.
    - Every constant present in both runs has the same axiom set.
  - The headline `levinNPHard_L3COL` and both `…_unconditional` corollaries are
    `[propext, Classical.choice, Quot.sound]`.
  - The `sorry` control reports `[sorryAx]`.
- **N4** (`N4Strip`, re-run on the check head): the same result as above. The landing proof passes
  with the matcher axiomatized, the delivered proof fails, and both matchers together fail
  (information).
- **`ProbeH12`** (the worker's probe, unchanged): rc 0, with 0 errors.
- **Canonical coe-A seals.** The collector `Collect` (recipe template, 12 owners) ran with rc 0.
  `mkseals_coe.py` (A variant, unmodified, `SEAL_CHUNK=1000`) generated the seals. Every part has its
  install and end records.

  | Owner | Requests | Errors |
  |---|---|---|
  | `Relations` | 191 | **0** |
  | `Verifier` | 2,150 | **0** (F08 closed; phase 2 had 1) |
  | `CircuitWitness` | 4,805 | **0** |
  | `Gadget` | 1,052 | **0** |
  | `UnaryArith` | 1,059 | **0** |
  | `ColoringGraph` | 1,942 | **0** |
  | `ColoringParse` | 2,550 | **0** |
  | `ColoringWitness` | 1,854 | **0** |
  | `Soundness` | 2,550 | **0** |
  | `Padding` | 1,847 | **0** |
  | `Hardness` | 4,865 | **0** |
  | **`Bridge`** (the recorded exception) | 2,478 | **43 errors on 20 lines** |

  - **`Bridge`, attributed.** Each of the 20 lines is one reader:
    - the 17 `rfl`/`Iff.rfl` readers, with 1 error each;
    - `syntaxStep_eq` (12), `edgeRelation_gadget_literal` (12) and `edgeRelation_literal_gadget` (2).

    That is 17 + 12 + 12 + 2 = 43. The seven `simp [EdgeRelation]` readers pass sealed. The count equals phase 2's no-unseal
    control `BridgeNone` (43).
  - The request counts equal phase 2's, except `Hardness`, which is +2, from new matcher definitions in
    its import closure.
- **Seal B** (`SEAL_EVAL=1`, `PolyExpr.eval` sealed too): each owner has one more request (e.g.
  `Verifier` 2,151, `Hardness` 4,866).
  - The 11 non-bridge owners give **0 errors**, `Verifier` included. Phase 2 had 1.
  - `Bridge` has the same 43 errors on the same 20 lines as coe-A.
  - So no proof reads `PolyExpr.eval` by defeq: LE-h12-arith reads it through `PolyExpr.eval_pow`/`eval_var`.
- **Strict seals.** The worker's 11 whole-file seals were moved onto the landing sources by
  `git merge-file` (old source, new source, sealed copy). Each insertion is the worker's single seal line.
  - **11/11 rc 0, 0 errors.**
  - **Bridge minimal unseal** (`BridgeMin`, phase 2's file moved the same way, +82 lines): rc 0, 0 errors.
- **Paired controls** (phase 2's `mkctl.py` and `ctl-pairs.tsv`, 50 pairs, one per new public
  definition; no definition was removed): **ALL_OK**.
  - `Ctl_sealed` has exactly 50 errors, one at each NEG line, and none at a POS line or anywhere else.
  - `Ctl_open` has 0 errors.
- **Explicit-unfold scan** (the gate-04 `scan.py` with the `G04Collect` tables, rc 0):
  - **7 hits**, exactly phase 2's seven `simp [EdgeRelation]` lines of `Bridge.lean`, now at lines 182,
    187, 192, 199, 209, 231 and 238. The docstring is 16 lines longer.
  - **0 hits outside `Bridge.lean`.** (c2) 0, (c3) 0.
  - LE-h12-strip's `…match_1.eq_N` references are in `refine` terms, not in lemma lists, and they are
    equation lemmas of a matcher, not of a definition. So the scan's rules do not list them. They are
    the route the F08 fix asked for, and the N4 probe checks them.
- **decls2** (pinned `decls2.py`, `fa81981a`):
  - **Landing head against `bff0567b`** (14 files): **242 ADDED, 0 CHANGED, 0 REMOVED**. That is the
    delivery's 245 minus the three deleted helpers. The statement text of the other 242 rows is
    identical.
  - **Worker commits alone** (`393c5cc1` against `bff0567b`): 245 ADDED, byte-identical to phase 1's
    `my-decls2.txt`.
  - **Per maintainer commit:**
    - LE-h12-arith: 3 REMOVED.
    - LE-h12-strip, LE-h12-bridge and LE-h12-doc: empty.
- **Lint.** `campaign_style_lint --check8b` on `TCSlib/Cryptography`, run on exports of the records tip
  `fb57a36c` and of the check head `a3617cde`.
  - **92 FAIL / 103 WARN** for both (540 and 553 files). The FAIL/WARN line sets are **identical, raw**,
    so there is no new FAIL or WARN.
  - `style_lint.py` on the 14 files: **0 findings**.
- **Sizes.** The files run from 59 to 720 lines (`ColoringParse` 720, `ColoringGraph` 675), all at most
  100 characters wide.
- **Lean slots.** Every start went through `runq.sh`, which checks `pgrep -fc "bin/lean "` ≤ 2 and at
  least 2,048 MB free disk (`check/slot.log`).
  - There was one queue at a time, on one olean tree. The host had no other Lean process during the
    job, so there was no wait, and nothing was killed.
  - Free disk stayed between 5.5 and 5.9 GB.
- **Source trees untouched.** `$SP/olean-replay-efh12` still state-checks 1469/1469 OK at `63d619e8` at
  the end. Snapshot #11 `snapmap verify` gives 0/0/0, RESULT OK, at the end (1,487 files).

## Notes

- **The count of Complexity readers.** The EF-H12-R1 row (and this job's dispatch) speaks of "the 11
  Complexity readers". The bridge has 10 readers of the three Complexity owner files
  (`Formulas/CNF` 2, `Formulas/CNFEncoding` 7, `DAGCircuitSat` 1). `levinNPHard_iff` is the 11th
  non-course reader. The total is 27 = 10 + 1 + 16, and the docstring states it that way.
- **Foreign generated names in source.** LE-h12-strip names `Turing.FinTM.stripLastTM_computes.match_1.eq_1`
  and `eq_2`. They are realized as private equation lemmas in `Verifier`'s environment, and the
  canonical seal treats them as theorems. The other route, `split`/`simp`, reduces the matcher by
  defeq and fails N4. The cleaner long-term fix is an owner-side named function and reader for
  `computesFunInTime_stripLast` in `Build/Primitives.lean` (follow-up).
- **The `ZeroKnowledge.lean` facade** gains the [St73] References entry and a reworded bullet (F4,
  adopted). In phase 1 the delivery's change to this existing file was the three inserted lines.
- **[AB09] entries without an in-text citation.** After F07(c), `Gadget.lean` and `UnaryArith.lean` list
  [AB09] in References without citing it in their text. This follows the disposition literally ("drop
  '(§2.3.)'"). Dropping the two entries is a possible gate item.
- **The strict seal lines are the worker's candidate lists.** They do not name `divNum`/`modNum`, which
  `UnaryArith` and `ColoringGraph` now use. The canonical coe-A seal requests every TCSlib definition
  of the closure, these two included, and gives 0 for both owners.
- **Open findings on record:** F05(d) (the top `SHA256SUMS` does not list `evidence/SHA256SUMS`) and the
  F06 near-relatives (ledger) stay as recorded. I1–I6 are information.

## State after the job

- **Kept for the Codex gate:**
  - `$SP/land-efh12/replay`: the olean tree accepted at check head `a3617cde`. Its state is
    `$SP/land-efh12/check/state.json`.
  - `$SP/land-efh12/mergewt`: the scratch worktree at `a3617cde`, with the probes and seal copies under
    `EFH12Land/`.
  - `$SP/land-efh12/wt`: the landing worktree on `land/ef-h12-levin-3col`.
  - `$SP/land-efh12/dwt`: the decls2 checkout.
  - `$SP/land-efh12/lint`: the lint exports.

  Delete them after the gate, with `git worktree remove` for the three worktrees.
- **Superseded:** phase 2's `$SP/olean-replay-efh12` (only read and hard-linked here) and the worktree
  `$SP/efh12/p2/wt`. Their owner may delete them once the gate no longer needs phase 2's tree.
- **Records:** `$SP/land-efh12/check/`:
  - `plan/`, `build/`, `permod.*`, `stateplan-*`, `statecheck-*`, `snapverify-*`, `slot.log`;
  - `decls2/`;
  - `rule10/`: probe runs, `seals-coe-{A,B}.tsv`, seal runs, controls, `g04cand/` and
    `unfold-scan-pre.txt`.

  `$SP/land-efh12/probe-src/` holds the probe sources (`N4Strip.lean`, `AxiomsLand.lean`, the moved
  `Strict/` and `BridgeMin.lean`). `$SP/land-efh12/{runq.sh,rule10.sh}` are the drivers.
- **Not done:** no PR, no commit to the records branch, no force push.

## Draft PR body

Use base `cryptography/pass-shelat-ch2-4` and head `land/ef-h12-levin-3col`, and open it as a **draft**.

Title: `EF-H12: Levin NP-hardness of 3-colouring with efficient reductions`

```markdown
Efficiency wave 1, job EF-H12 (`ef-h12-levin-3col`). It proves `LevinNPHard L3COL R3COL` with no hypothesis: every
language with a witness relation has a Levin reduction to `(3COL, R_3COL)` whose instance map and witness map are
`PolyTimeComputable` string maps with exact output lengths. With it, the two ZK theorems of [PS10, Theorem 124.1]
hold without their `LevinNPHard` hypothesis.

**Not stacked.** The base is the records branch, and this PR depends on no other open PR. Its diff is 23 commits and
14 files, +4,068/−0: 13 new files under `ZeroKnowledge/LevinHardness/`, plus the `ZeroKnowledge` facade.

## Contents
- **Route:** `(L, R) → (CKT-SAT, R_CKT) → (3SAT, R_3SAT) → (3COL, R_3COL)`.
  - The circuit route is [AB09, Lemmas 6.10 and 6.11], with the wire values as the witness [PS10, Theorem 124.1,
    step 2].
  - The 3SAT → 3COL step is Stockmeyer's reduction [St73] in the variant of the course file
    `NPReductions/ThreeSATToColoring.lean`.
  - Padding with isolated vertices gives exact lengths.
- **Files:**
  - `Relations` defines `R_CKT` and `R_3SAT`.
  - `Verifier` is step 1: the certificate, the verifier in `P` and the tableau instance map.
  - `CircuitWitness` is step 2: the Tseitin map with the wire-value witness.
  - `Gadget`, `UnaryArith`, `ColoringGraph` and `ColoringParse` give step 3: the gadget instance map and its
    polynomial-time tests.
  - `ColoringWitness` is step 4: the explicit colouring witness.
  - `Soundness` is the course theorem, transported along a homomorphism; it is not re-proved.
  - `Padding` pads graphs and colourings.
  - `Hardness` holds `levinNPHard_L3COL` and `zk_proof_of_{witnessRelation,mem_NP}_of_owp_unconditional`.
- **`Bridge.lean`** is a bounded, recorded Rule-10 exception (decision-log row "EF-H12-R1 ruled (A)", ledger
  DL-65). It holds exactly 27 readers of definitions in files this PR may not edit:
  - 10 for `Formulas/CNF`, `Formulas/CNFEncoding` and `DAGCircuitSat`;
  - `levinNPHard_iff` for `ZeroKnowledge/NP.lean`;
  - 16 for the course file.

  17 are `rfl`/`Iff.rfl`, and 10 are case lemmas, as its docstring says. Each group is repaid by an owner PR (below).

## Commits
1–19. The worker's 19 commits, applied with `git am`. Authorship and messages are kept, and the tree after commit
   19 equals the phase-2 check head's (`efdd41d8…`).
20. `4230f872` **LE-h12-arith** (EFH12-F02; EF-H12-R3 (B)). `unaryPow_poly`, `unaryDiv_poly` and `unaryMod_poly` are
    deleted. The call sites use `unaryPolyOf_poly` and `divNum_poly`/`modNum_poly` with `divNum_eq`/`modNum_eq`.
21. `76676c14` **LE-h12-strip** (EFH12-F08). `polyTimeComputable_stripCert` reads the catalog's `match` through its
    matcher's equation lemmas, not by defeq. A kernel check with that matcher replaced by an axiom accepts it and
    rejects the delivered proof.
22. `ad07b07c` **LE-h12-bridge** (EFH12-F01; EF-H12-R1 (A)). The bridge docstrings cite the decision-log row, name the
    owners and the repayment, and mark the case lemmas.
23. `11f33ef3` **LE-h12-doc** (EFH12-F05(c), F07). The citation fixes from the [AB09] ch. 2/6 ingest (Def 6.9 →
    Def 6.1, the TCSlib reading convention, the "§2.3" tags on glue files). [St73] is cited for the Karp form and
    the reduction (Theorem, p. 22; proof pp. 21–22; Fig. 1, p. 24), with a deviation note on
    `levinNPHard_L3COL`.

All 23 commits are signed.

## Checks
- **Maintainer review:** ACCEPT WITH LANDING EDITS, with phase 2 passed
  (`briefs/efficiency-gaps/wave1/EF-H12/final-r1/`). All its landing edits are applied; the landing record is
  `landing.md`.
- **Merged-tree replay of the landing head** with the records tip (Lean = `bff0567b` + U12/U13), on a copy of
  phase 2's state-checked tree:
  - 27 modules rebuilt with rc 0 and 0 errors, including root `TCSlib` and `audits/pass-shelat/Checks`. The 15
    `sorry` warnings are the records side's GSW admissions; the EF-H12 modules have 0 `sorry` and 0 warnings.
  - The state check gave 1469/1469 OK.
- **Axioms:** all 488 constants stored by the 12 modules and the facade are within
  `{propext, Classical.choice, Quot.sound}`. The headline and both corollaries are
  `[propext, Classical.choice, Quot.sound]`.
- **Canonical coe-A seals:**
  - **0 errors on all 11 non-bridge owners**, `Verifier` included (F08 closed).
  - `Bridge.lean`, the recorded exception, has 43 errors on 20 readers, the definitional readers, as
    expected. The 7 `simp [EdgeRelation]` readers are the scan's 7 hits.
  - Seal B gives the same result. The worker's strict seals pass 11/11, the bridge's minimal unseal passes, and
    the 50 paired controls are ALL_OK.
  - Explicit-unfold scan: 0 hits outside `Bridge.lean`.
- **decls2** against the base: 242 added, 0 changed, 0 removed. That is the delivery's 245 minus the three deleted
  helpers.
- **Lint:** no new FAIL or WARN, and `style_lint` reports 0 findings on the 14 files.

## Still to do
- **A Codex gate is to be staged** for this PR. It also does the Codex source review of the AB09 ch. 2/6, GJS74
  and St73 ingests (`blueprint/src/references/`), whose anchors are "awaiting Codex source review".
- **Follow-ups, not in this PR:**
  - The **Complexity owner PR** adds the bridge's 10 `Formulas/CNF`, `Formulas/CNFEncoding` and `DAGCircuitSat`
    readers, EF-H1's `mem_PRIMES`/`mem_PRIMESBin`, and the DL-70 readers. After it merges, the bridge rows
    are deleted and their consumers re-pointed.
  - The **course-file owner PR** (EF-H12-R2 (B)) adds the 16 readers, makes `sat3Coloring` public with its
    properness lemma, and adds the [St73] References line with the gadget-variant note. Then the bridge's course
    section and the re-derived properness proof are dropped.
  - `levinNPHard_iff` moves into `ZeroKnowledge/NP.lean` after #390 merges.
  - The sorried FormulaKit rows (`Emit.lean:216-271`) are queued for their owner.
  - Information, for the Complexity owner: the catalog statement `computesFunInTime_stripLast` also uses a private
    matcher of `Build/Primitives.lean`, which no seal can cover. A named function with a reader beside that row
    would let `polyTimeComputable_stripCert` avoid reducing it.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
```
