# Gate 51 · io-phfe checkpoint 4 (statements r2) · in-house Lean verification r2

**Verdict: PASS, with three notes.** This replay is the first time r2 has been elaborated. The worker ran static checks only.

- **Source.** The 37 delivered patches reproduce **every one of the worker's 37 commit hashes**
  on the base, ending at `073d0a5a`. `src/` equals that tree byte for byte (88/88). The r1 head
  `a4fe0fd7` (checkpoint 3) is reproduced on the way.
- **Build.** All 89 changed/new modules and their downstream elaborate. That is the 88 owned
  modules plus root `TCSlib`, and the 302-module closure. Every module has rc 0 and 0 errors.
  There are exactly **33 `sorry` warnings**, equal per file to the static count and to r1's.
  r2 adds no admission.
- **Axioms.** There are 0 non-standard axioms over all 2,347 stored constants of the 86 new
  modules.
  - Every one of the 51 changed and 8 added r2 declarations is **standard-only**, except
    `wee20PHFE_gjls21`. That one carries `sorryAx` only transitively, through the admitted
    security headline `wee20PHFE_simSecure`.
  - The four new concrete bound lemmas are proved, not admitted.
- **Repairs.** All of them check mechanically against `findings-r1.md`: R1, R2, R3, G51-05 and
  G51-09, plus minors G51-01, 06, 10 and 11.
- **Freeze.** Against checkpoint 0, the declarations whose header or opening prose changed are
  **exactly the 51 names** of the worker's authorized table. That is r1's 16 plus r2's 35, and
  the changed fields agree 51/51. There are 0 removals.
- **Notes.**
  - **N1:** two new linter warnings (unused binder `hHonest`).
  - **N2:** `state_bounded` is stated through `List.ofFn`. This is a necessary adaptation to r1's
    fixed-width state, so the field is satisfied by `stLen`.
  - **N3:** `SimTargets` carries the four bounds as target fields although proved lemmas
    discharge them.
  - Details are in §5. None is a defect against the specs.

Run on 2026-11-19, 00:46–01:02 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`, and the work
directory is `$SP/io-r2/`.

- **Evidence:** `verification-r2.zip`, beside this file. Its SHA-256 is in
  `verification-SHA256SUMS`, and it holds an inner `SHA256SUMS` over 172 files.
- **Constraints observed:**
  - no `lake build`, no cache get;
  - Lean ran only through the recipe's `runner.py`, `runner_full.py` and `mathlibextra.sh`, on a
    `cp -al` copy, with one Lean process of this job at a time;
  - nothing was written into `$SP/olean-snapshot*` or an existing replay tree. The
    checkpoint-0 tree rehashes 0/0/0 after the build and at the end, and snapshot #11 verifies
    0/0/0 at the end;
  - no commit, push or branch was made. The scratch git work used the private bare repository
    `$SP/io-r2/git.git`, with the repository objects as alternates;
  - no script from the delivery was run.
- **Host slots.** Before each start, `pgrep -c -x lean` gave:
  - 0 at the Mathlib extra and the build start;
  - 2 (foreign) at each probe start, so the total was 3 of 3.
  - Foreign Lean processes rose to 2 during the build, also 3 of 3 in all. They were not touched.

## Expectations against results

| # | Check | Expected | Result |
|---|---|---|---|
| 1a | Checkpoint folder | intact | `SHA256SUMS`: **137/137 OK**. The file set equals the list (138 files with `SHA256SUMS`). Exchange commit `883b51a9` adds only these 138 files under `inbox/fills/io-phfe/`. `REPORT.md` = `18b69e60…d501`. `PENDING-RESUME.patch` = `366321a7…ca49`, as REPORT states. It is not applied in `src/` |
| 1b | base + patches | source HEAD `073d0a5a` | `replay_patches.sh` (unchanged from checkpoint 0) reproduces **all 37 hashes of `COMMITS.tsv`**: `25f1af12` … `70b85f9b` (checkpoint 0) … `a4fe0fd7` (r1) … **`073d0a5a3ff88d958f94c2ae50a67bc92476f616`**, tree `d3cbabf22596ab02450f036d8f2cecb42063a533` |
| 1c | `src/` against the tree | byte for byte | **88/88** `src/` blobs equal `073d0a5a:<path>`; the path sets are equal |
| 1d | Changed paths against the base | 86 new + 2 facades | **86 A + 2 M** (`Pairing.lean`, `AdvancedEncryption.lean`); **19,487** lines; **33** `sorry` tokens, all outside comments. r1 (`a4fe0fd7`) also has 33, per file identical. r1→r2 touches 19 files (+407/−130), with one new module, `Wee20/Targets/CircuitEfficiency.lean` |
| 2a | Plan | — | `downorder`: 88 changed, 89 down, `order-noroot` **302**. `fullorder`: 1544. `stateplan plan` against the checkpoint-0 tree's state gives **89 to build** (77 rebuilt checkpoint-0 modules and 12 modules new since then) and 1455 reused. Closure: 88 built, 214 reused |
| 2b | Build | every module rc 0, 0 errors | **89/89 rc 0**. `error:` 0, `error(` 0, substring "error" 0. Run 00:51:31–00:57:29Z, 358 s of module time, peak maxrss 4.58 GB (root) |
| 2c | `sorry` warnings | 33, none added | **33**, per file equal to the static counts: `LinearSecurity/Endpoint` 3, `LinearSecurity/Theorems` 6, `PHFE/Adapter` 2, `PHFE/Headlines` 4, `PHFE/Security` 8, `QuadraticSecurity/Compose` 2, `QuadraticSecurity/Theorems` 8. The other 81 modules have 0 |
| 2c' | Other warnings | — | **86** linter warnings across 19 new modules (§2). Two are new in r2 code (N1). The rest are in modules or lines that r2 does not touch, or predate it |
| 2d | State check | RESULT OK | `stateplan update` 89/89 taken. `check` **1544/1544 OK** (full order) and **302/302 OK** (closure); again at the end |
| 2e | Link counts | rebuilt oleans have 1 link | **89/89 link count 1**. Exactly 89 non-Mathlib files have link count 1, plus 1 Mathlib extra. The tree holds 1590 files and 3346 symlinks |
| 2f | Start tree | untouched | `$SP/olean-replay-ioc0-phfe`: state check **1532/1532 OK** before use. Rehash baseline `336b89d5…`: **0/0/0** after the build and at the end, with check OK at the end |
| 3 | Axioms | standard, plus `sorryAx` only where an obligation is upstream | **78 `#print axioms` targets** (51 changed + 8 added + headlines + 3 proof/sketch-only). **65 standard-only, 13 `sorryAx`, 0 other** (§3). Control: `[sorryAx]` |
| 3' | Census | — | 86/86 modules, **2,347** stored constants: **2,313 standard-only, 34 via `sorryAx`, 0 non-standard**. Of those, **33 are direct holes**, all public theorems and equal to the 33 `sorry`s. The 1 transitive-only constant is `wee20PHFE_gjls21`. **No definition, structure or target depends on `sorryAx`** |
| 4 | Repairs | R1–R3, G51-05, G51-09 as specified | all PASS (§4) |
| 5 | Freeze against checkpoint 0 | changed headers ⊆ the authorized set | Changed header or opening prose: **exactly the 51 authorized names**, the worker's `changed-headers.tsv`; fields agree 51/51. Removed 0; added 60 (§5) |

## 1. Source reconstruction

- **Inputs.** The delivery is exchange `883b51a99a1fbe1e94e5c04f293fc42ec47eec20`, folder
  `inbox/fills/io-phfe/checkpoints/checkpoint-4-r2/`. Its base is `iO/phase-a-base` at
  `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`.
- **The 37 rebuilt commits** exist only in `$SP/io-r2/git.git`, on no ref. All 37 hashes match,
  so every commit message, author and date in the series is bound. `source/replay-am.txt` lists
  each patch's commit and tree.
- **Folder contents.** `PENDING-RESUME.patch` and `RESUME.md` are unapplied proof-development
  material, as REPORT describes. They play no part in `src/` or in this replay.

## 2. Replay (snapshots.md job recipe, on the checkpoint-0 replay tree)

**Start tree.** `$SP/olean-replay-ioc0-phfe` was state-checked 1532/1532 OK at `70b85f9b` and
rehashed as a baseline (4,923 entries). It was then copied with
`cp -al … $SP/io-r2/olean-replay-ioc4-r2`, which gave 1577 files and 0 with link count 1.

**Export.** `git archive 073d0a5a` of `TCSlib`, `TCSlib.lean`, `audits`, the lake files and
`scripts`: 1,696 files, with `.lake/packages` symlinked.

**Mathlib extra (environment, not delivery).** Since checkpoint 0, `PartialGarbling/Layered.lean`
imports `Mathlib.Data.Matrix.ColumnRowPartitioned`, which the pinned package build lacks.
- `mlmissing.py` confirms it is the only missing Mathlib root besides the two extras already in
  the tree (`Matrix.Hadamard` and `GeneralLinearGroup.Card`), and that all its imports are
  present.
- `mathlibextra.sh` compiled it into the replay tree only:
  - pinned source `d2a9004e…2aa9`;
  - rc 0;
  - olean `541493dd4fa3a97211ef4cc69746129b3ecc1a7e2c50c287c6de20bd27e63089`.

**Build.** A single run, with no stop.

**Warnings other than `sorry`** (86):

| Kind | Count |
|---|---:|
| unused `simp` argument | 45 |
| unused variable | 36 |
| unused `_` name suggestions | 2 |
| unused automatically included section variable | 1 |
| tactic never executed | 1 |
| `ring` does nothing | 1 |

| File (under `FunctionalEncryption/` unless `Pairing/`) | Warnings | r2? |
|---|---:|---|
| `Pairing/MatrixDH/ColumnLaws` | 27 | no (post-M0 proof file) |
| `Wee20/PHFE/Raw` | 14 | no: the checkpoint-0 unused `κ`/`pp`/`f` at lines 67–76. The r2 addition `wee20PHFE_raw_value_bounded` is clean |
| `Wee20/PHFE/Simulator` | 14 | no: the checkpoint-0 lines 60–78. The two r2 lemmas are clean |
| `Pairing/MatrixDH/SelfReduction` | 6 | no |
| `PartialGarbling/Layered`, `Wee20/QuadraticCorrect` | 4 each | no |
| `Wee20/PHFE/Correctness` | 3 | no |
| **`Wee20/Targets/CircuitEfficiency`** | **2** | **yes: unused variable `hHonest` at lines 58 and 82 (N1)** |
| `Wee20/LinearSimulator` | 2 | no |
| `Wee20/PHFE/Encodings` | 1 | in an r2-edited `simp` list (`quadraticSimState_injective`, line 464). `eq_self_iff_true` is unused. That argument predates r2. This replay cannot tell whether r1 already warned |
| `Wee20/Targets/MatrixDH` | 1 | no: the checkpoint-0 unused `f` (now line 76) |
| `Classes`, `SemiAdaptive/{Data,Games}`, `PartialGarbling/Defs`, `Pairing/MatrixDH/{Defs,Diagonal,FiniteLinear}`, `Wee20/LinearSecurity/Slack` | 1 each | no |

## 3. Axioms (`probes/Heads.lean`, `runner_full.py`, no `-o`; final attempt rc 0)

The only warning is the control's `sorry`. The control prints `[sorryAx]`.

- **Standard-only, `[propext, Classical.choice, Quot.sound]` or a subset (65).**
  - 50 of the 51 changed declarations (all but `wee20PHFE_gjls21`, below).
  - All 8 added declarations: `CircuitLinearEfficient`, `circuitLinearEfficient_iff`,
    `PHFE.valueEncoding_length_le`, `wee20PHFE_raw_value_bounded`,
    `wee20Sim_raw_state_bounded`, `wee20Sim_raw_value_bounded`,
    `wee20SASim_raw_state_bounded` and `wee20SASim_raw_value_bounded`.
  - The correctness headlines: `wee20PHFE_raw_correct`, `wee20PHFE_raw_correctExcept_zero`,
    `wee20PHFE_correct` and `wee20PHFE_correctExcept_zero`.
  - The three proof/sketch-only changes: `mddhRealizable_of_preTarget`,
    `PHFE.quadraticSimState_injective` and `PHFE.quadraticSimState_length`.
- **Via `sorryAx` (13). All are admitted security results. None is an r2 addition.**
  - `wee20PHFE_saSimAdv_le` and `_simAdv_le`;
  - `_saSimAdv_dlin_le` and `_simAdv_dlin_le`;
  - the four `wee20PHFE_raw_*SecureWith`;
  - `wee20PHFE_simSecure`, `_saSimSecure`, `_subexpSimSecure` and `_subexpSASimSecure`;
  - `wee20PHFE_gjls21` (changed by G51-02).
  - `gjls21` is **not** a direct hole. In the census its only `sorryAx` route is the conjunct
    `wee20PHFE_simSecure`, which is admitted in `PHFE/Headlines`. Its correctness conjunct and
    the new circuit conjunct are standard-only.
- **Census** (`probes/Census2.lean`: the checkpoint-0 memoized collector, run over the 86 new
  modules).

  | Population | Constants | Standard-only | Via `sorryAx` | Other axiom |
  |---|---:|---:|---:|---:|
  | All stored constants | **2347** | **2313** | **34** | **0** |
  | Public (non-private, non-internal, non-auxiliary) | 1819 | 1785 | 34 | 0 |
  | Public theorems | 980 | 946 | 34 | 0 |
  | Public definitions, structures, constructors | 839 | 839 | 0 | 0 |

  At checkpoint 0, 39 definitions (bundles, simulators) and 4 target structures inherited
  `sorryAx`. At r2 none does.

## 4. The repairs, against `findings-r1.md`

**R2 — G51-03.** Verdict: PASS.
- **Fields.** `state_bounded` and `value_bounded` exist in **both** `FEScheme.Raw.Simulator` and
  `FEScheme.Raw.SASimulator`, in the context `{C : FnClass} (S : FEScheme.Raw C)`. Four
  `example`s state the fields in the spec's form and close by the projection.
  - `value_bounded` is **verbatim** the spec:
    `∃ b : PolyExpr, ∀ κ (pp : PublicParams S.G κ) (v : C.Out κ (S.cprm κ pp)), (C.encValue κ (S.cprm κ pp) v).length ≤ b.eval κ`.
  - `state_bounded` reads `(List.ofFn (encSt κ pp st)).length ≤ b.eval κ`. The spec's
    `(encSt κ pp st).length` does not typecheck after r1, which made `encSt` a fixed-width
    `Fin (stLen.eval κ) → Bool`. The adapter is the canonical one (N2).
- **Targets.** `SimTargets` has the four matching fields, `sim_`/`sa_` × `state_bounded`/
  `value_bounded`.
  - Their types are the interface fields at the concrete `S`, `Sim` and `SASim`.
  - `simTargets_iff` is the ten-conjunct reader.
  - The pure assemblies `wee20Sim` and `wee20SASim` attach `hT.sim_*`/`hT.sa_*`, and they
    elaborate.
- **Concrete proofs: all four proved, none admitted.**
  - `wee20Sim_raw_state_bounded` and `wee20SASim_raw_state_bounded` give the witness `stLen` by
    `List.length_ofFn`.
  - `wee20Sim_raw_value_bounded` and `wee20SASim_raw_value_bounded` reuse
    `wee20PHFE_raw_value_bounded`, with witness `G.wG.add (const 1)`, via
    `PHFE.valueEncoding_length_le`. That lemma uses `Nat.size_le_size`, `Nat.size_pow` and
    `BB1Machine.order_le_two_pow`.
  - All are standard-only.
  - Four `example (hT : SimTargets …) : type_of% hT.<field> := <lemma> …` probes elaborate, so
    each target field is discharged by its lemma.

**R3 — G51-04.** Verdict: PASS.
- `tools/io-r2/r3check.py` finds **30/30** `SamplesEfficiently` applications in the 88 files.
  Each first argument has the form `fun κ … => NUPPT.advInput κ (…)`, with the same κ. They are
  in:
  - `FEScheme`: 4;
  - `Simulator` and `SASimulator`: 3 each;
  - `SchemeTargets` and its reader: 4 + 4;
  - `SimTargets` and its reader: 6 + 6.
  This is 20 logical maps and 30 occurrences, as reported.
- `r3args.py` compares each occurrence with r1:
  - arguments 2–4 (draw encoding, output encoding, core) are **unchanged** in all 30;
  - argument 1 is exactly `NUPPT.advInput κ` applied to r1's map.
- `pubGen_eff` is the spec's `fun κ (d : GroupDescription G κ) => NUPPT.advInput κ d.val`. The
  `#check @FEScheme.pubGen_eff` shows it. An `example` restating the spec's full
  `SamplesEfficiently` closes by `S.pubGen_eff`.
- `#check` of all 21 sampler fields and readers elaborates.
- `NUPPT.advInput n y = pairEncode (List.replicate n true) y`. No other sampler contract
  (`DrawSamplable`) is used in the owned files.

**R1 — G51-02.** Verdict: PASS.
- **Statement.** `#print Wee20.CircuitLinearEfficient` gives the following order of quantifiers
  and conditions:
  1. `∃ q : PolyExpr`;
  2. `∀ ℓ n d κ`, so one polynomial comes before all dimensions, the degree and κ;
  3. `pp : PublicParams G κ`, typed and therefore supported;
  4. `pk` with an honest-setup witness `∃ ρ, (PHFE.setupCore … pp ρ).1 = pk`;
  5. the guard `0 < ℓ + n`;
  6. `∃ N, ∃ C : BoolCircuit.MultiDAGCircuit N`, so pp and pk are fixed before the circuit and
     the circuit before all inputs;
  7. `C.IsFaninTwo ∧ C.size ≤ (ℓ + n) * q.eval κ`, with `size = N + gates.length` (inputs and
     gates counted);
  8. `∀ x y (ω : Quadratic.EncDraw G κ pp)`, with input
     `List.ofFn x ++ List.ofFn y ++ Wire.quadraticEncDraw pp ω`, `input.length = N`, and
     `C.eval (input.getD · false) = List.ofFn (PHFE.encCT … (PHFE.encCore … pp pk x y ω))`.
     This is the exact encoded `encCore` output.
- **Fit with the spec.** This matches R1 clause by clause. The input/gate size convention is
  stricter than gates only.
- **Reader.** `circuitLinearEfficient_iff` is `Iff.rfl`.
- **Targets.** `Targets.circuitLinear : CircuitLinearEfficient G` is a new field, and `targets_iff`
  has six conjuncts. `LinearEfficient` is retained.
- **Headline.** `wee20PHFE_gjls21` concludes
  `… CorrectExcept 0 ∧ … SimSecure ∧ Wee20.CircuitLinearEfficient G`. An `example` takes `.2.2` of
  it at type `CircuitLinearEfficient G`.

**G51-05.** Verdict: PASS.
- `#print Wee20.MddhPreTargets` gives `∀ p hp (d ℓ : PolyExpr), ∃ f, PolyTimeComputable f ∧ ∀ κ ω c, …`,
  with no `NUPPT` binder. The same holds for `mddhPreTargets_iff`.
- A grep for `_D` over the 88 files finds 0 matches. Checkpoint 0 had 2.
- The link `mddhRealizable_of_preTarget` changed in its proof and sketch only, and is
  standard-only.

**G51-09.** Verdict: PASS.
- **Grep.** `foldr pairEncode`, matched across line breaks, gives 21 at checkpoint 0, **25 at r1**
  (with the two `List.foldr_cons/nil` lists in `Encodings`) and **0 at r2**.
- **Replacements.** `PrivateKeyScheme.encodeList` appears 29 times: the 25 replacements plus
  `encodeList_cons`/`encodeList_nil` in the two `Encodings` `simp` lists. By file:
  - `WireDraws` 18;
  - `Simulation/Games` 4;
  - `PHFE/Encodings` 4;
  - `Defs/Simulator` 2;
  - `PHFE/Simulator` 1.
- **Imports.** `EnsembleSecurity` is newly imported by `Defs/Simulator` and `PHFE/Simulator`.
- **Equivalence.** The probe
  `(fun l => l.foldr pairEncode []) = PrivateKeyScheme.encodeList` (by induction) passes. The
  changed `_eq` readers re-elaborate.

**Minors.**
- G51-01: the `SimSecureWith` docstring now states the familywise reading. Its formal body is
  unchanged, as the freeze field `prose` shows.
- G51-06: REPORT W6 row (line 307); 1−(1−½)(1−¼)(1−⅛) = 43/64, which is 344/512.
- G51-10: `Pairing.lean` no longer cites AGW20 or IW14 (0 hits).
- G51-11: REPORT names `1e77173a` as the delivery and freeze start.
- G51-07 and G51-08 are promotion requests with no source change. They were not checked here.

## 5. Freeze against checkpoint 0, and notes

**Method.** `tools/io-r2/declfreeze.py` reads the source text. Each column-0 declaration gets its
namespace-qualified name. It records three fields:
- the **header**: the statement up to `:=` for theorems, and the whole declaration for
  definitions and structures;
- the **opening prose**: the docstring before its `**Proof sketch` marker;
- the **sketch**.

**Results.**

| Comparison | Old | New | Added | Removed | Header/prose changed | Sketch-only | Body-only |
|---|---:|---:|---:|---:|---:|---:|---:|
| checkpoint 0 → r2 | 1171 | 1231 | 60 | 0 | **51** | 12 | 100 |
| r1 → r2 | 1223 | 1231 | 8 | 0 | 40 | 1 | 2 |
| checkpoint 0 → r1 | 1171 | 1223 | 52 | 0 | 16 | 11 | 100 |

- **Agreement with the worker.** The 51 changed names are **exactly** the 51 rows of the
  worker's `evidence/changed-headers.tsv`. The changed fields (`header` / `prose` /
  `header,prose`) agree on **51/51**.
- **Every name maps to a relayed item:**
  - r1 PHFE-C0-F01: 16;
  - G51-09: 23 (`Omega.encode`/`_eq`, `viewWordBits`/`_eq`, `viewWord_eq`, and 9
    `Wire.*` draw/state pairs);
  - G51-04: 3 (`FEScheme`, `SchemeTargets`, `schemeTargets_iff`);
  - G51-03: 2 (`wee20Sim`, `wee20SASim`);
  - G51-02: 4 (`Targets`, `targets_iff`, `wee20PHFE_gjls21`, and the prose of
    `LinearEfficient`);
  - G51-05: 2;
  - G51-01: 1 (prose).
  - Several names carry more than one item: `Simulator`, `SASimulator`, `SimTargets` and
    `simTargets_iff` (R1 + G51-03 + G51-04), and `wee20SASim_raw` (R1 + G51-09).
- **r1 → r2.** The figures match REPORT: 40 record changes, 8 new declarations, and 3
  proof/sketch-only changes (`quadraticSimState_injective` and `_length` bodies,
  `mddhRealizable_of_preTarget` sketch).
- **Checkpoint 0 → r1.** The 16 changed names are r1's authorized set.
- **The 12 sketch-only names** against checkpoint 0 are permitted proof-sketch edits from the
  proof milestones. Of them, 11 come from r1 or earlier and 1 from r2.

**N1 (note).** `CircuitLinearEfficient` and its reader bind the honest-setup hypothesis as
`(hHonest : ∃ ρ, …)`. The name is never used, so Lean warns twice. The statement is unaffected
(the binder is a non-dependent hypothesis). Write `(_ : ∃ ρ, …)` or an arrow at the next
checkpoint.

**N2 (note).** `state_bounded` uses `(List.ofFn (encSt …)).length`, because r1 made `encSt`
fixed-width. The field therefore always holds with `b := stLen`, and adds nothing beyond r1. This
is consistent with R2: the spec was written against the checkpoint-0 list-valued `encSt`, and
the finding accepts r1's fixed width. The substantive r2 addition is `value_bounded`.

**N3 (note).** `SimTargets` requires the four bound fields as Phase B targets, as R2 asks. They
are not Phase B obligations, though: the four proved lemmas discharge them (§4, the `type_of%`
probes). The assemblies `wee20Sim` and `wee20SASim` read the bounds from `hT` rather than from
the lemmas. This is harmless. An optional simplification is a reader
`SimTargets.of_samplers`, or dropping the four fields in favour of the lemmas, but the spec
asked for the fields.

## 6. State after the run

- **Kept.** `$SP/io-r2/olean-replay-ioc4-r2` is the accepted r2 tree.
  - Its own files are 34.7 MB: the 89 rebuilt oleans plus the `ColumnRowPartitioned` extra. The
    rest are hard links into `olean-replay-ioc0-phfe` and Mathlib symlinks.
  - `stateplan check` 1544/1544 OK at the end.
  - It is kept because free disk stayed above 2.4 GB at the end: **7,199 MB**.
  - The work directory, excluding the tree, is 102 MB.
- **Not touched.**
  - `$SP/olean-replay-ioc0-phfe`: rehash 0/0/0 and check OK at the end;
  - `$SP/olean-snapshot`: snapshot #11 map `e7bb03b4…`, verify 0/0/0 at the end;
  - other jobs' trees and processes.
- **Disk incident (mine; disclosed).**
  - Free space was 2,770 MB at the start.
  - The first source export was a `git archive` of the whole tree at `073d0a5a`. That tree
    includes the records' large non-Lean files, so the export took **2.3 GB**. Free space fell
    to **431 MB**, below the 2,000 MB stop line, for about one minute, shortly before 00:51Z.
  - I saw it on the next `df`, which was taken together with the cheap `cp -al`. I deleted the
    export at once, and free space returned to 2,737 MB.
  - No Lean process of this job was running. Every later step used the path-restricted export
    (38 MB).
  - Other jobs may have been near the disk limit during that minute. I do not know of any
    failure.
- **Probe attempts.** `Heads` failed twice before passing. Both failures were probe-side: an
  `open Turing` was missing, and the namespace of `layeredPG_raw` was wrong. The source was not
  involved. All three logs are kept in the zip, under `logs/probes/{attempt1,attempt2,final}`.
  `Census2` passed on attempt 1, with an unchanged source.
