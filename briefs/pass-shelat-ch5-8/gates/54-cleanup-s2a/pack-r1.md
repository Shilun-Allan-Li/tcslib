# Gate 54 · the cleanup Stage 2 S2-A gate: PR #390 · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). **Gate 54** is the
one Codex gate that Q-A10 (a) gives job S2-A of cleanup Stage 2 ("one PR for S2-A …, one Codex gate";
`cleanup-stages.md` § *S2-A rulings Q-A1 to Q-A11*). One open draft PR is audited.

- **PR #390** ([link](https://github.com/Shilun-Allan-Li/tcslib/pull/390)), branch `cleanup/stage2-s2a`, head
  **`9f7f409c2e09749428db75b9ddd324f92695e4af`** (tree `df1952ed048de92371cb6f754d65dbbbdf6eff7d`, `TCSlib` tree
  **`ae345736160511e6d3e7d8b47ad76c430c424500`**), base branch `cryptography/pass-shelat-ch2-4`. **S2-A base** (its merge
  base with the records tip) **`61a5f0fb640622c15fdd33df56efa470b2bf26c8`** (`TCSlib` tree `849ee945…`, Lean-equal to
  olean snapshot #10's T `cf6a2266`). 43 SSH-signed commits; **63 files, +1,650/−897**, all under `TCSlib/`. GitHub's
  REST `base.sha` (`f0f7f528…`) is a records tip read when the PR was last updated; the diff in this pack is from the
  merge base, which is GitHub's three-dot view.
- **Records pin:** the commit that files this directory, `briefs/pass-shelat-ch5-8/gates/54-cleanup-s2a/`.
  `dispatch-r1.md` and the prompt name it. Since the S2-A base, the records branch merged Lean only through the GSW 6b
  statements (#376/#377) and the U12/U13 fills (#392): **12 Lean paths, none of them an S2-A path**. The records tip
  replayed here is `8836292693d7c611ee375d162f34766841635337` (`TCSlib` tree `745bf4b494b6581a5666ef9ca0a6e735a68ddcef`);
  the records tip at staging, `a25338e0f78290dff74a754ba89a2988655ac046`, is records-only on top of it (same `TCSlib`,
  `TCSlib.lean`, `audits/`, toolchain, manifest and lakefile; `source-head-r1.json`). The pin is records-only on top
  of that.
- **Merged tree.** `git merge-tree --write-tree 88362926 9f7f409c` is clean, tree `84c0205e003688519b1bd13156066d09d0ebe6b4`,
  `TCSlib` tree **`73af3ec6968e023e87ce00af649db0e2e02f4353`**. The maintainer replayed it as the scratch commit
  `62c2794272bd5cbe4fe3f031d4186924e4e1a222` (parents `88362926`, `9f7f409c`; **on no ref, never pushed**). Its `TCSlib`
  is S2-A's 63 files blob-equal to the head and the records side's 12 files blob-equal to the tip, nothing else
  (`verification-r1.md` §1). `merge-tree(a25338e0, 9f7f409c)` has the same `TCSlib` tree.
- **Mathlib** `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, **Batteries** `39260e31b7b3f7f05643da95242463b462dc05f1`
  (`lake-manifest.json`, unchanged by the PR), toolchain `leanprover/lean4:v4.25.0`.

Paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/` or `briefs/`. `S2/` is
`briefs/pass-shelat-ch5-8/cleanup-stage2/`. Line numbers are at the head.

## How this gate runs (standing rules 17 and 18)

- **Cloud, reading only.** Every input is in the repository: the records branch at the pin and the PR branch.
  Nothing is needed from Seyoon's machine, and nothing is on the exchange (S2-A was done in-house; there is no worker
  delivery).
- **No Lean, no cache.** The auditor does not run `lean`, `lake` or `lake exe cache get`, and builds nothing. The
  maintainer's in-house evidence is the build evidence: the four batch reports (`S2/s2a-d1-report.md` …
  `s2a-d4-report.md`) and the merged-tree verification of this directory (`verification-r1.md`,
  `verification-r1.zip`). The audit grades that evidence by reading.
- Python as `python3 -I`; `git`, `sha256sum`, `unzip` and reading tools only. Mathlib/Batteries source may be read at
  the pinned revisions (GitHub, or a blob-filtered fetch), never built.

## Scope

S2-A is plan jobs **J0** (foundations: promotions and readers), **J1** (Complexity hosts and derandomization) and
**J2** (the Asymptotic layer) of Stage 2: Rule-10 readers, the seal fixes that use them, and the ruled body and
header repairs, so that the Pass–shelat owners pass the canonical seals without unfolding another file's definitions.

- **The plan:** `S2/s2a-workplan-r1.md` (§0 pins and method; §1 the items with exact statements; §1.3 the 14
  statement-level rows; §1.4 the definition bodies) and **`S2/s2a-items.tsv`, 435 rows**, one per item, with step,
  owner, line at the plan tip, kind, freeze status and exact intended change. 425 rows come from `S2/scope.tsv`
  (job J0/J1/J2); 10 are new (S2A-N01..N10).

  | kind (`s2a-items.tsv` column 8) | J0 | J1 | J2 |
  |---|---:|---:|---:|
  | seal fix (proof-only) | – | 128 | 136 |
  | B-only fix, proof-level (15 of J2's are **definition bodies**, Q-A2) | 1 | 2 | 77 |
  | B-only fix, statement-level (freeze exceptions, Q8) | – | – | 11 |
  | B header fix, statement-level (Q-A3) | – | – | 3 |
  | add reader | 13 | – | 9 |
  | promote (DL-43, DL-55, DL-57, DL-59) | 4 | – | – |
  | re-point | 1 | 3 | 15 |
  | alias change (DL-35 #1, #2, #3, #6; #2 moved to S2-D by Q-A1) | – | – | 4 |
  | delete (`host_*`; DL-38 `ofFn_chunk`, `fac_ofFn_halves`) | – | 1 | 2 |
  | citation fix (PS10 Tier A; one Tier B advisory) | – | 19 | 2 |
  | doc fix / doc nit / records correction | 4 | – | – |

- **Four ruled additions after the plan** (decision log, 2026-11-18): Q-D2-1 (A) the reader `epsClose_iff`; Q-D2-3,
  Q-D3-1 (A) five proof sketches and `OneWayYao` under 1,000 lines (docstring-only); Q-D2-4 (A) the private
  `invProbAt_glPad_eq` in place of the twice-written local `hbridge`; Q-D2-5 (B) `SIS/CollisionOutput`'s
  `@[simps!]` replaced by explicit field lemmas. Also Q-D1-1 (two "step 4" labels, in A38) and Q-D1-3 (DL-62, records).
- **Commits** (`source-head-r1.json` `commits`): D1 = A01–A18 (18, `70503f3c` … `c119a3c4`); D2 = A19–A36, A38 (19,
  `75b04bd0` … `a1545eae`; A30 partial, A37 none); D3 = A37 `31608312`, A30 rest `dff281b5`; D4 = `27cbdeb0`
  (Q-D2-1), `d6fd4bb5` (Q-D2-3/Q-D3-1), `96918135` (Q-D2-4), `9f7f409c` (Q-D2-5). One commit per step; each message
  lists its rows.

**Out of scope** (mention only if something in scope depends on it):
- **S2-B, S2-C, S2-D and Stage 3**: their rows, including the consumer-side copies that S2-A's promotions leave for
  S2-B to re-point (DL-56, DL-57, DL-59/DL-40), DL-35 #2 (S2-D, Q-A1), the J3 seal residue in
  `Pseudorandom/Generators/Asymptotic/FromPermutation`, and the size splits queued for Stage 3 (`OneWay` 1,095 lines,
  `Factoring` 1,924, `Collections` 1,177 and the files already over 1,000 at the base; Q-D2-3, Q-D3-2).
- **The records side of the merge** (GSW 6b statements, Gate 46; U12/U13, Gate 53): only the merge interaction.
- **Handed-off files**: `TCSlib/Complexity/TuringMachine/Encoding.lean` (DW-10 Q1; S2-A only inserts the Q11 readers).
- **Rule 15** (efficiency claims): S2-A adds no hypothesis; check only that no restated header adds or drops one.

## What changed

**Public API** (decls2 over the 63 files, base vs head; `verification-r1.zip:checks/decls2-base-vs-head.tsv`,
mapped row by row to `s2a-items.tsv` in `checks/decls2-to-items.tsv`: **0 unmapped**):
- **41 ADDED**: 37 readers and promotions of the plan, the DL-55 move's ADDED side, and the three D4 additions
  (`epsClose_iff`; `rawCollisionInputs_fst`, `_snd`, which replace the `simps!`-generated lemmas of the same names and
  statements). Each one's proof term: `checks/added-proofs.tsv`. 23 are `rfl` (19) or `Iff.rfl` (4).
- **15 CHANGED** (statement level): `Games.extTape`, `_of_lt`, `_of_not_lt`, `_update` (`{C : Type}` → `{C : Type*}`,
  DL-59/Q8); `EnsembleLemmas.exists_copiesRed`, `take_drop_ofFn_blocks` (DL-35 #1/#3); `Ensemble.copies_X`,
  `FunFamily.ofFn_ofString_f`, `ofString_id_f`, `prod_f`, `PermFamily.toFunFamily_f` (`@[simp]` kept, Q-A8),
  `Candidates.fmult_f`, `fmult_inv_factor` (Q8 freeze exceptions, workplan §1.3 rows 1, 5–8, 10, 11); `FunFamily.glPad_f`,
  `glBit_append` (Q-A3, rows 12–13).
- **4 REMOVED**: `Complexity.IterateFind.host_dispatch`, `host_branch`, `host_halt` (S2-RP-004, DW10-Q9); the
  `TrapdoorPredictor` side of the DL-55 move of `decide_singleton_eq_true` (same full name, now in
  `Foundations/BitLists`).
- **Private** (decls2 does not track them): headers restated `Collection.collInverter_success`, `fiber_le`
  (rows 2–3), `ofFn_oddCoins` (row 4), `fac_prodInverter_eq_yaoB` (row 9), `invProbAt_reduction_ge` (row 14); added
  `oddParam_eval` (S2A-N07) and `FunFamily.invProbAt_glPad_eq` (Q-D2-4); deleted `fac_ofFn_halves` (DL-38); kept and
  re-proved `ofFn_chunk` (the plan's fallback, D2 §3 item 1).
- **Definition bodies changed** (Q-A2, 15): `FunFamily.prod`; `PermFamily.toFunFamily`, `toFunFamily_domEquiv`,
  `toFunFamily_codEquiv`; `Ensemble.copies`; `Collection.owfFamily`, `Collection.glPad` (proof field only);
  `FunFamily.glPad`, `glBit`, `glInverter`, `glPad_inEquiv`, `glPad_outEquiv`; `Candidates.fmult`, `plantFactor`;
  `oddCoins`.
- **Attributes, imports** (`checks/added-scan.txt`, `checks/simp-*.txt`): the set of `@[simp]` declarations in the 63
  files is unchanged except the removed `@[simps! (config := { isSimp := false }) fst snd]`; 0 added `sorry`, `admit`,
  `native_decide`, `axiom`, `set_option`, `attribute`; one added import,
  `Hashing/FromDiscreteLog/Probability` → `Games.Bridges.Experiments` (planned, S2-RP-031); the 5 added `unfold`s name
  definitions of their own file (`unaryMulFun`, `owpPredMachine`, `glPadInvMachine`, `glPadCollInvMachine`, `yaoRaw`).

**Everything else is proof-only or docstring-only**: 264 seal fixes, the B-only proof fixes, re-points (DW-5's
`hdisp`/`hbranch`/`hhalt` to `host_*_view`; DL-47, DL-55 T1; DL-35's proof uses; Q-A7 (b) `DyadicUniform`'s three
`bitsTo*_uniform` from `FinDist.map_uniform_equiv`), the PS10 citation fixes (J1's 19 Tier A sites: A1 "step 4" →
"final paragraph of the proof" at 17, A2 at `SeedMajority.lean:83` and `RootSchedule.lean:16`; Q-D1-1's two further
labels; S2-PA-29 and the Tier B advisory S2-PR-06 in A20), the G49-01/G49-02 `Games/Relational` docstrings, and D4's
five sketches and `OneWayYao` trim.

## Rulings and records in force

1. **Stage 2 rulings** (Seyoon, 2026-11-17; `cleanup-stages.md` § *Stage 2 rulings*; plan `S2/plan-r1.md`): Q1 four
   jobs, S2-A in-house; **Q2** the 51 statement-level seal-B-only fixes in their owner jobs, each checked by its gate;
   **Q7** duplicate public definitions get the promoted forms; **Q8** widen `Games.extTape` to `Type*`. **DW-10 final
   rulings** (same file): **Q8** fix all 194 SEAL-B-ONLY rows, freeze exceptions granted for meaning-preserving
   statement changes "stated through `PolyExpr.eval`'s readers, listed individually … and checked by its gate";
   **Q9** delete the uncalled `host_*`; **Q11** the two provider readers in `Encoding.lean` as pure insertions.
2. **S2-A rulings Q-A1 to Q-A11** (Seyoon, 2026-11-18; `cleanup-stages.md` § *S2-A rulings*; workplan §5): Q-A1 (a)
   DL-35 #2 to S2-D; **Q-A2 (a) the 15 definition bodies are freeze exceptions, casts only through `PolyExpr.eval_*` or
   published `*_eval` readers, each with an `rfl` old-body = new-body probe in the evidence**; **Q-A3 (a)** `glPad_f`,
   `glBit_append`, the private `invProbAt_reduction_ge` restated (§1.3 rows 12–14), `glPad_f_equiv`/`glBit_equiv`
   re-proved from them; Q-A4 (a) the Q11 reader is `CodeTM.toFinTM_computesInTime_iff`; Q-A5 (a) the
   `InteractiveHandler.rU_eq`…`rS_eq` readers; **Q-A6 (b)** `Games.zeroBits_eq_cast` in `Games/BitCodec.lean`;
   **Q-A7 (b)** S2-RP-088 done; Q-A8 (a) `toFunFamily_f` keeps `@[simp]`; **Q-A9 (a)** restatements keep binders at the
   family's own `PolyExpr` type, with `Fin.cast` through published readers or equivalences; Q-A10 (a) one PR, one
   gate; Q-A11 (a) the DL-55 move stays in S2-A.
3. **Batch rulings** (decision log `PassShelatChapter5-8Plan.md`, rows of 2026-11-18/19): Q-D1-1 (a), Q-D1-2 (a),
   Q-D1-3 (a) (DL-62); Q-D2-1 (A); Q-D2-2 (a) (batch D3); Q-D2-3, Q-D3-1, Q-D3-2 (A); Q-D2-4 (A); **Q-D2-5 (B)**: "fix
   `SIS/CollisionOutput.lean:53` in D4 … explicit `@[simp]` field lemmas or a `splitCoins` reader, whichever keeps the
   public API; its seal goes to 0"; Q-D2-6 (A); Q-D4-1 (a) (operational: disk freed, replay resumed).
4. **Rule 10** (`policy.md` §1; DW-10 W1–W7): another file's TCSlib definition is read only through published readers;
   core/Mathlib definitions may reduce in `rfl`/`decide`/`show` steps; canonical **coe-A** seals are the check, coe-B is
   run and attributed. Reducible abbreviations are notation; DW-10 Q3: the `FinDist` coercion is notation.
5. **Duplication** (`policy.md` § *Duplication*; `briefs/pass-shelat-ch5-8/duplication-ledger.md` DL-35, DL-38, DL-43,
   DL-47, DL-55–DL-57, DL-59, DL-62; precedents G44-01, G45-01, G48-01): disclosure is not acceptance; an undisclosed or
   unaccepted re-proof or restatement of a public TCSlib, Batteries or Mathlib lemma, including an inline
   re-derivation, is a **major**.
6. **Policy** (`policy.md`): formula docstrings (statement prose first), source tags or a glue statement, a
   `**Proof sketch.**` for every nontrivial proof (the campaign threshold is about 20 lines), files 150–600 target and
   < 1,000 lines unless a split is recorded.
7. **PS10 citations**: `briefs/pass-shelat-ch5-8/ingests/ps10-cite-check-final-r1/REPORT.md` (Tier A corrections and
   Tier B advisories). PS10 ch. 2–4 and the appendix are ingested (`blueprint/src/references/pass-shelat-2010-*.raw.md`);
   ch. 5–8 are not, so ch. 5–8 tags are graded against the cite-check report.
8. **Standing rules** `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2 (3, 5, 15, 17, 18).

## Questions for the audit

**A. Readers.** For each of the 37 planned additions and `epsClose_iff` (`checks/added-proofs.tsv`, workplan §1.1 and
the TSV rows): is it the ruled statement (names per Q-A4, Q-A5, Q-A6 b), a **true definitional reader** (`rfl` /
`Iff.rfl`, or a one-line `rw` through the owner's own readers for the `sidSpec_*`, `prod_*_eval`,
`owfFamily_inLen_eval`), placed **beside the definition it reads**, with a formula docstring, and not `@[simp]`? Is any
"reader" in fact a new lemma that needs its own proof, or does it read a definition of another file (Rule 10)? The
non-`rfl` additions deserve a full read: `polyTimeComputable_iterateFind_elim` (`convert … using 2; cases … <;> rfl`),
`yaoRaw_eq` (`funext; unfold yaoRaw; cases … <;> rfl`), `pairDecode_singleton`, `decide_singleton_eq_true` (moved
verbatim? compare with the base's `TrapdoorPredictor.lean:143–145`), `zeroBits_eq_cast`, `mul_prob_le_expect` (the
pinned Stage 1 header; proof as `Lamport/Averaging.lean:129`), and the two `rawCollisionInputs_*` lemmas.

**B. Body casts (Q-A2).** For each of the 15 changed definition bodies: does the cast go only through `PolyExpr.eval_*`
or a published `*_eval` reader (D3's `fmult` names its length equation with a term-mode `have`, D3 §3 item 2), and is
the new body `rfl`-equal to the old one? Grade the probes (`verification-r1.zip:batches/d2/qa2/`, `batches/d3/qa2/`):
12 in D2 (`QA2.lean`, against D1-head bodies, which equal the base's for these 12 — check) and 3 in D3; negative
controls `QA2Ctl`, `QA2FCtl`, `QA2GLCtl` fail with Type mismatch. Are the `_d1` copies verbatim? Is any probe vacuous
(e.g. `Collection.glPad` compared as a whole structure with its proof field)?

**C. Restated headers.** For each statement change (15 CHANGED + 5 private headers): is the head header **exactly**
the ruled restatement of workplan §1.3 (rows 1–14), DL-35 #1/#3 (S2-BK-01/03), DL-59 (S2-DL-10) and Q-D2-5, with
binders at the family's own `PolyExpr` type (Q-A9 a), and is it meaning-preserving (every instance of the old
statement an instance of the new, and conversely for `Fin.cast` along `rfl`-provable equations)? Are `glPad_f_equiv` and
`glBit_equiv` re-proved from the new forms (Q-A3)? Did any header change that is not listed (compare the base and head
headers of every declaration in the 63 files, not only decls2's)? Does `toFunFamily_f` keep `@[simp]`, and were its
downstream `simp` uses probed (A24, D2 §3 item 7)?

**D. Proof-only rows and deletions.** Spot-check the seal fixes and B-only fixes against their TSV text (at least the
`needs-check` rows: S2-SL-089, S2-SL-108, S2-SL-280, the `EnsemblesLemmas`/`HardCore/Functions`/`OneWayYao` ones), the
re-points (S2-RP-001..003, DL-47, DL-55 T1, S2-RP-030/031, Q-A7 b), the `host_*` deletion (no caller left; docstrings
re-worded), the DL-38 deletion, and the PS10 Tier A texts against the cite-check REPORT. Is any change outside its ruled
row (e.g. a proof restructured beyond what the seal needs, A30's larger `fac_strong_key`/`exists_plantFactorer` local
bounds, D3 §3 items 3–4)? Is D4's `d6fd4bb5` docstring-only, as claimed (code identical with comments stripped)?

**E. Seal residues.** The canonical coe-A at the head is 0 on every S2-A owner sealed, except the disclosed residues:
- `Encryption/PublicKey/TrapdoorPredictor` 2/2 (`tdpPredictor_runAtL`, `uprob_tdpPredictor`: S2-B's S2-SL-270..273;
  D1 §2);
- `TCSlib/Complexity/TuringMachine/Encoding` 4 (handed-off file; D1 §2);
- downstream `Pseudorandom/Generators/Asymptotic/FromPermutation` A 2 / B 19 (job J3's rows S2-SL-313..315, S2-BO-002,
  009, 155..163; the same errors line for line on D2's tree (run in D3), at D3, at D4 and on the merged tree).

Is that list complete? Each batch sealed the owners it touched (D1 26, D2 40, D3 4, D4 11); is any S2-A owner left whose
last seal predates a later change to it or to a file it reads through? Grade the seal evidence: collector, the archived
Gate 06/10 instrumenter unmodified, the gated runner (`lean -DmaxErrors=0`, no `-o`), the A/B dedup, the base runs, and
the errors mapped by enclosing declaration (`tools/errdecl.py`). On the merged tree the 11 coe-A seal sources are
byte-identical to D4's modulo the probe-package name, and the results are D4's (`verification-r1.md` §6).

**F. No unplanned public declaration; scope.** Is every decls2 row a ruled item (`checks/decls2-to-items.tsv`)? Are the
two new private declarations within their rulings (Q-D2-4: "one private lemma beside `glPad_inEquiv_ofFn`, with
docstring and source tag"; D4 placed it after the four `glPad` string lemmas, D4 §3)? The diff's 63 files are the 61
`TCSlib` owner files of `s2a-items.tsv` (column 5; all touched) plus `Games/BitCodec.lean` (Q-A6 b) and
`InformationTheory/Extractors.lean` (Q-D2-1) (`checks/items-owner-files.txt`, `checks/diff-files.txt`): is every
change in a file inside its ruled rows? No `blueprint/`, `audits/`, facade, toolchain or manifest change.

**G. Duplication** (binding; ruling 5).
- Is any new reader or promoted lemma a restatement of an existing public TCSlib, Batteries or Mathlib lemma
  (search by name and by statement shape at the pinned revisions)? Same-short-name hits at the merged tree:
  `checks/shortname-hits.txt` (20 names with more than one hit). The known ones are ledgered promotions whose
  consumer-side copies S2-B/S2-D remove: `sidSpec_dom_*`/`_rng_*`, `zeroBits_eq_cast` (DL-57,
  `BonehBoyenSecurity/Lazy.lean`), `rU_eq`…`rS_eq` (DL-56, `BonehBoyenMachine/Words.lean`'s own `BB1Machine.rU`…),
  `extTape` (DL-59/DL-40, `AdaptiveCPA/Hybrid.lean`). Are those dispositions right?
- **Staging observation S-1 (for you to grade).** After DL-35 #3, `EnsembleLemmas.take_drop_ofFn_blocks`
  (`Asymptotic/EnsemblesLemmas.lean:436`) and the public `MultiMsg.take_drop_ofFn_blocks`
  (`Encryption/PrivateKey/FromPRF/ReductionMachine.lean:311`, which imports `EnsemblesLemmas`) have the same statement and
  the same proof term `(FunFamily.ofFn_blocks q s w ⟨i, hi⟩).symm`. Both predate S2-A (at the base the first was stated
  through the local `blocks` alias); no ledger row and no batch report mentions the pair. Grade it (an old duplicate made
  literal by a ruled alias change; precedent DL-62 ledgered an old duplicate found by D1 for Stage 3).
- The in-file `hbridge` (D2 §4) is now the private `invProbAt_glPad_eq` (Q-D2-4): is no copy left, and is it no
  restatement of a public lemma? D1's local `have`s in `ModuleHost` (`stop_step`, `pad_run`), D3's `hv` pair and local
  reindexings (D3 §4), and the reports' searches: anything they missed?

**H. Docstrings, sketches, attribution** (`policy.md` §2–§3). Every new or restated public declaration: statement prose
first; a source tag where the item is "a result" (e.g. `[PS10, Def 181.1]` on `epsClose_iff`, `[PS10, Theorem 87.3]` on
`invProbAt_glPad_eq`), otherwise a glue statement — do `rawCollisionInputs_fst/_snd` (no tag, no "Glue.") meet §2?
Every proof of about 20 lines or more has a `**Proof sketch.**` (D4 added five; is any other S2-A proof now over the
threshold without one?). Are the PS10 Tier A/B citation edits the cite-check REPORT's texts? Sizes: `OneWayYao` 999
lines (D4), the Stage 3 splits as ruled. **Staging observation S-2:** six added lines are 101–103 characters
(code points; `Asymptotic/Collections.lean:966`, `HardCoreCollection.lean:125`, `:426`, `OneWay.lean:387`, `:473`,
`Candidates/RSA.lean:367`), none replacing a line that was already over 100. All six come from D2 steps (A24, A28,
A31, A34), and D2 §2 says "every added line is at most 100 characters". `policy.md` sets no width rule (the campaign
convention is 100); grade the report statement.

**I. Evidence and its binding** (§ *Evidence binding*). Grade the four batch reports and `verification-r1.md`: does
each claim follow from the evidence in `verification-r1.zip`? Does each piece bind to the head (`9f7f409c`) or, for the
merged tree, to `TCSlib` tree `73af3ec6`? The batch evidence directories live on the maintainer's host; the ZIP carries
their manifests (`batches/*/SHA256SUMS`, all re-verified at staging) and the pieces a reading audit needs. A missing or
non-binding piece of necessary evidence is a **major**.

**J. Is anything undisclosed?** Among the commits, the PR description (the current body is stale draft wording;
`pr390-description-r2.md` is the replacement the maintainer posts before dispatch), the batch reports and the records,
is any change, claim or omission undisclosed? The known slips are below.

## Evidence binding

| Evidence | Bound to | What it shows | Reaches the PR head by |
|---|---|---|---|
| `S2/s2a-d1-report.md` … `s2a-d4-report.md`; batch evidence `$SP/s2a-d{1,2,3,4}/` (manifests `dfab3215…`, `7d0ecfda…`, `35e6dcf7…`, `51d39684…`, re-verified 0 failures at staging) | the batch heads `c119a3c4`, `a1545eae`, `dff281b5`, `9f7f409c` | per-step file checks; replays (snapshot #10 → D1 → D2 → D3 → D4 trees); state checks; admissions; decls2; Q-A2 probes; seals with base comparisons; lints | D4 is the head; D1–D3 are its ancestors, and each later replay rebuilt every module whose source closure changed |
| `verification-r1.md`, `verification-r1.zip` (SHA-256 in `verification-SHA256SUMS`; inner `SHA256SUMS`) | scratch merge `62c27942` (`TCSlib` tree `73af3ec6`) = merge-tree(`88362926`, `9f7f409c`) | merged replay 28 built / 1,428 reused, all rc 0; state check 1,456 OK; admissions; coe-A seals of the 11 D4 owners; lint delta; curated batch evidence | `73af3ec6` contains the head's 63 S2-A blobs; recompute `git merge-tree --write-tree <pin> 9f7f409c` and read its `TCSlib` tree |
| this pack's `source-head-r1.json`, `pr390.diff.txt`, `pr390-description.md` | the head, the base and the records tips | pins, the 43 commits (parents, trees, signature kind, files), per-file statistics at base and head, record hashes | git objects only |

## Known dispositions and slips (not findings)

- **Report slips.** D2 §2's decls2 table cites `copies_X` as S2-BO-041 (it is S2-BO-001; S2-BO-041 is the `copies` body)
  and the four `OneWay` headers as "S2-BO-006/007/073/080" (they are S2-BO-072, 073, 076, 084). The workplan §1.1 lists
  `owpGen_apply`, `owpPair_apply`, `owpGenNot_apply` as "S2-RD-26/27/28"; the TSV numbers them RD-27, RD-28, RD-26.
- **History edits before push**, disclosed: A09 and A10 amended and re-signed after the D1 lints (D1 §1); A30 (D3) and
  Q-D2-4 (D4) amended once to re-wrap long lines. A37 was committed before A30's rest (D3 §1).
- **Signatures**: all 43 commits carry an SSH `gpgsig` header of the account's shared Claude key (BS-F08); none was
  cryptographically verified (no allowed-signers file).
- **Q-D2-5 wording**: the ruling says "explicit `@[simp]` field lemmas … whichever keeps the public API". D4 wrote the
  two lemmas **without** `@[simp]`, as the generated ones were (`isSimp := false`), and they are no longer `rfl`
  lemmas (D4 §1, item 4). Grade whether that is the ruled option.
- **D4 replay interruptions**: a container restart and a disk-guard stop; the resume rule re-verified every completed
  olean (D4 §2).
- **The merged-tree replay** started from D4's tree, not snapshot #11; its first attempt failed in 0.03 s before Lean
  ran (worktree without `lean-toolchain`) and was set aside (`verification-r1.md` §3).
- **PR description**: the body at staging (`pr390-description.md`) is draft-stage text (head `dff281b5`, 62 files,
  pending rulings). `pr390-description-r2.md` replaces it before dispatch.
- **No seal B on the merged tree** (coe-A is canonical; D4's coe-B results stand, and no S2-A owner's closure changed in
  the merge: `verification-r1.md` §6).

## Merge interaction (maintainer merge conditions, not audit items)

- #390 × the records tip: `merge-tree` clean; `TCSlib` tree `73af3ec6`; replayed (`verification-r1.md`).
- **Adoption:** the merged replay tree (`$SP/g54/olean-replay-g54`, state checked over 1,456 modules) is a candidate
  olean snapshot for the merge commit, if the records tip's Lean is still `745bf4b4` at merge time.
- Open PRs touching S2-A paths are the maintainer's to sequence (S2-B/C/D are not dispatched yet).

## Files of this directory

- **`pack-r1.md`** (this file) and **`dispatch-r1.md`** (the Codex prompt; postdates the pin; not in `SHA256SUMS-r1`).
- **`pr390.diff.txt`**: `git diff 61a5f0fb640622c15fdd33df56efa470b2bf26c8 9f7f409c2e09749428db75b9ddd324f92695e4af`
  (= `git diff <records tip>...9f7f409c`, byte for byte, since `61a5f0fb` is the merge base).
- **`pr390-description.md`**: the PR body at staging (REST `.body`, raw). **`pr390-description-r2.md`**: the replacement
  body.
- **`source-head-r1.json`**: pins, Lean equality, the merged tree, the 43 commits, per-file statistics (blob, SHA-256,
  lines, width, over-100, tabs, trailing spaces, `sorry` tokens, micro sign) at base and head, the manifest revisions,
  and the SHA-256 of every record this pack cites at the records tip at staging.
- **`verification-r1.md`**, **`verification-r1.zip`**, **`verification-SHA256SUMS`**: the merged-tree replay and the
  staging checks (`checks/`), with the curated batch evidence (`batches/`).
- **`SHA256SUMS-r1`**: every file above other than `dispatch-r1.md`.

## Findings delivery

Return **`findings-r1.md`** as Markdown in the Codex chat (a ZIP with `findings-r1.md` at its root if you have search
logs or scripts). Push nothing, write nothing to the repository, open no PR, comment on nothing. The user dispatches and
merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Number the findings **G54-01, G54-02, …**. Grade the staging observations S-1 and S-2 and the batch reports D1–D4 in a
separate table. Report the audited head, the records pin, the verification ZIP's SHA-256 as you computed it, the
searches you ran (with hit counts), the counts by severity, and a verdict for **PR #390**:
- **CLEAR:** zero blockers and zero majors.
- **HOLD:** otherwise.

**Severities**
- **blocker:** a false or unusable statement; a restated header that is not meaning-preserving; a changed body that is
  not `rfl`-equal to the old one; a change outside S2-A's rows that alters a statement or deletes a used declaration.
- **major:** any of the following:
  - a statement or body change not ruled (not in workplan §1.3/§1.4, the TSV or the D-rulings), or a ruled one not
    made as ruled;
  - an unplanned public declaration;
  - a forbidden read (Rule 10) not covered by the rulings, or an undisclosed seal residue;
  - an undisclosed copied private lemma, or an undisclosed (or unaccepted) re-proof or restatement of a public one,
    including an inline re-derivation of a TCSlib, Batteries or Mathlib lemma;
  - a fabricated or wrong source tag;
  - necessary evidence that cannot be verified or does not bind to the PR head.
- **minor:** documentation or API defects, including an inaccurate formula docstring, glue note, proof sketch, report
  statement or PR description.
- **note:** anything else.
