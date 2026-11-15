# Fill learning — final

**Unit** `learning` · **Worker** Claude · **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317`
(`cryptography/pass-shelat-ch2-4`) · **Proof branch** `fill/learning` (local), head
`f30d80f02` · **Lean** 4.25.0, Mathlib at the base's manifest.

## 0. Status

| Target | Status |
|---|---|
| `Randomness.predictAdv_prfConcept_negligible` (PS10 Thm 179.1 (b)) | **proved**; statement unchanged; axioms `[propext, Classical.choice, Quot.sound]` |
| `Randomness.not_weakLearnsUnder_prfConcept` (part (c), unchanged) | its axioms are now standard: `[propext, Classical.choice, Quot.sound]` |

Commits (the series in `patches/`, with `patches/COMMITS.tsv`):
1. `c323e6041` checkpoint 1 — the distinguisher and the real game (exchange `8318ce34f`);
2. `d80d3e5e3` checkpoint 2 — the random function (exchange `6ebe473c0`);
3. `f30d80f02` Theorem 179.1 (b) proved.

The final sweep of the supplied order with the four helpers inserted before the owned module has
0 errors, and the sorry census is `base-sorries.txt` minus `predictAdv_prfConcept_negligible`
(§6).

## 1. The proof

Fix `hF : PRF F`, a learner machine `A` and a polynomial `m`. Write `X = {0,1}^n`.

1. **The distinguisher and the real game** (`Learning/Sample.lean`, `Learning/Distinguisher.lean`,
   `Learning/Law.lean`). `LearnPRF.exists_learnDist`: a next-query machine `B` whose coins are, by
   a bijection, `m(n) + 1` points `ρ` and `A`'s coins `c`, and whose query tree with budget
   `m(n) + 1` against any oracle `g` evaluates to
   `decide (A(⟨S, ⟦ρ_m⟧⟩; c) = [true]) == firstBit (g ρ_m)`, with `S` the nested labelled examples
   `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩`, `j < m(n)`. `B` is the public non-adaptive query chain
   `MultiMsg.exists_queryChain_nuppt` (zero message vector) of the machine that computes the
   learner's input and the last label from the encoded tuple (`learnIn`, `lastLabel`: block map of
   `relabel` over the first `m(n)` blocks, polynomial-time), runs `A` on it
   (`NUPPT.exists_compParam`) and compares (`NUPPT.exists_seq` with the uniform machine of
   `verdictFun`). Then `exists_learnDist_acceptProb`: for every keyed family `G : K → X → X`,
   `acceptProb G (oracleDist (B.toOracleAdversary n n n (m(n)+1))) = gameProb (m n) G (learnerFn A n (m n))`,
   the uniform probability over `((k, (s, r)), x)` that the learner, on `s` labelled by
   `firstBit ∘ G k`, predicts `firstBit (G k x)` (coins relabelled by the bijection and
   `snocEquiv`). The prediction game is the same uniform probability (`predictSuccess_eq_uprob`:
   its law is the uniform law on the product, `iid_uniform`, `Rejection.uniform_prod`,
   `Rejection.uniform_probTrue`). In the owned file `learnerFn = learnerOf` (`learnerOf_eq`,
   `encodeSample_eq`) and `firstBit ∘ F n k = prfConcept F n k` (`prfConcept_eq`), so
   `predictSuccess (prfConcept F n) (m n) (learnerOf A n (m n)) = acceptProb (F n) D`.
2. **The random function** (`Learning/Random.lean`, `abs_gameProb_random_sub_half_le`): for
   `n ≥ 1`, `|gameProb m (fun R => R) ℓ − ½| ≤ m/2^n` for every learner `ℓ`. With `R` averaged first:
   at a fresh point `x ∉ s`, `flipAt hn x` (flip the first bit of `R x`) is an involution that keeps
   the examples' labels and negates `x`'s, so it exchanges winning and losing functions and the
   probability is exactly `½` (`uprob_flip_half`); otherwise it lies in `[0, 1]`. Hence
   `|gameProb − ½| ≤ Pr[∃ j, s_j = x] ≤ m · 2^{-n}` (`uprob_exists_le`, `uprob_eq_point`).
   With `randomFunction_apply`, this bounds `|acceptProb (randomFunction X X) D − ½|`.
3. **The bound** (owned file): for `n ≥ 1`,
   `predictAdv = |acceptProb (F n) D − ½| ≤ |acceptProb (F n) D − acceptProb R D| + |acceptProb R D − ½|
   ≤ prfAdv (F n) (D^{m(n)+1}) + m(n)/2^n` (`prfAdv_def`, `distAdv_def`, `abs_sub_le`). The sum is
   negligible: `PRF.negligible_prfAdv hF B (m + 1)`, and `m(n)/2^n = m(n) · (½)^n`
   (`EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`), `Negligible.add`; the
   eventual bound (`Negligible.mono` from `n = 1`) handles `n = 0`.

**Route deviation (no statement changed).** The brief's step 1 names T1 (non-adaptive queries)
and T4. The proof uses instead the public `MultiMsg.exists_queryChain_nuppt` of the §3.9 reduction
(`Encryption/PrivateKey/FromPRF/ReductionMachine.lean:461`), which already is a non-adaptive
next-query machine with points from its coins and a final verdict of an arbitrary machine on the
encoded tuple (`toOracleAdversary` at `ℓ₁ = ℓ₂ = n`): no handler or bridge proof was needed. The
probability bridge is the uniform-probability (`uprob`) layer: `acceptProb` is a `uprob`
(`acceptProb_def`), and the prediction game's `FinDist` law is the uniform law on the product; the
`ProbComp`/`trialDist`-as-oracle-run bridge suggested by the brief is not needed.

**Edge cases.** `n = 0`: steps 1 and 3 hold at every `n` (the single point, `firstBit` is
`false`); step 2 needs `n ≥ 1` and the final eventual bound starts at `n = 1`. `m(n) = 0`: no
examples (`Fin 0`), the encoded tuple is the last block alone, the union bound is `0`. A fresh
point equal to an example: no case split in step 1; it is the bad event of step 2. `A` printing
anything other than `[true]`: the prediction is `decide (… = [true])` throughout. The codecs'
timeout outputs: the query chain makes exactly `m(n) + 1` queries within the budget `m(n) + 1`,
and `B`'s verdict is the equation of `exists_queryChain_nuppt` for every oracle; no timeout is
reached. The coins: `B`'s coins are, by the bijection, `m(n) + 1` `n`-bit points (`(m(n)+1)·n` bits,
blocks of `FunFamily.blocks`) and `A`'s coins (the composed machine has `A.coins + 0`, relabelled by
`finCongr`).

## 2. Changed and new files

| File | Lines | Role |
|---|---|---|
| `TCSlib/Cryptography/Randomness/Learning.lean` (owned) | 220 | the proof of part (b) |
| `TCSlib/Cryptography/Randomness/Learning/Sample.lean` | 259 | the learner's input and the last label from the encoded tuple |
| `TCSlib/Cryptography/Randomness/Learning/Distinguisher.lean` | 136 | the distinguisher |
| `TCSlib/Cryptography/Randomness/Learning/Law.lean` | 173 | the game probability, both games |
| `TCSlib/Cryptography/Randomness/Learning/Random.lean` | 203 | the random-function bound |

Every line ≤ 100 characters, every file ≤ 1000 lines (`logs/final-width.log`). Import graph:
Sample ← Distinguisher ← Law ← Random; Sample imports `FromPRF/ReductionMachine` and
`GGM/Reduction`; Law imports `Randomness/Extraction/Rejection` and `LearningTheory.PAC`. The owned
file imports the four helpers (the facade). No helper imports the owned file; none of the imported
modules is downstream of the owned file (all precede it in `order.txt`, and the sweep checks the
order with the helpers inserted).

**Owned-file edits.** Title (dropped "(statement phase)"); `## Main results` (part (b) proved); a
new `## Contents` (the helpers); four imports; the target's docstring sketch rewritten to the
delivered proof (three steps, the deviation from T1); the target's body. The statement, every other
declaration (including part (c) and its proof), the statement prose and the simp attributes are
unchanged.

## 3. New declarations

All in namespace `TCSlib.Cryptography.Randomness.LearnPRF`; each public one has a docstring with
its formula, and each proof of 15 lines or more a `**Proof sketch.**`.
- Sample: `foldr_pairEncode_nil`, `firstBit` (`firstBit_eq`), `tupleWord` (`tupleWord_eq`),
  `relabel` (`relabel_eq`, `polyTimeComputable_relabel`), `sampleLen` (`sampleLen_eval`),
  `sampleOf` (`sampleOf_eq`), `lastPair` (`lastPair_eq`, `polyTimeComputable_lastPair`), `learnIn`
  (`learnIn_eq`, `polyTimeComputable_learnIn`), `lastLabel` (`lastLabel_eq`,
  `polyTimeComputable_lastLabel`), `learnIn_tupleWord`, `lastLabel_tupleWord`; private `blk`,
  `length_blk`, `relabel_blk`, `tupleWord_split`.
- Distinguisher: `verdictFun` (`verdictFun_eq`, `polyTimeComputable_verdictFun`),
  `exists_learnDist`; private `zero_add_fun`.
- Law: `iid_uniform`, `predictSuccess_eq_uprob`, `gameProb` (`gameProb_eq`), `learnerFn`
  (`learnerFn_eq`), `snocEquiv` (`snocEquiv_apply`), `exists_learnDist_acceptProb`.
- Random: `flip0` (`flip0_eq`, `flip0_flip0`), `firstBit_of_pos`, `firstBit_flip0`, `flipAt`
  (`flipAt_eq`, `flipAt_involutive`), `uprob_flip_half`, `uprob_eq_point`,
  `abs_gameProb_random_sub_half_le`.
- Owned file: none (the proof of the target).

No `@[simp]`; no new `abbrev`. Every new public `def` has an `_eq`/`_eval`/`_apply` reader (lint
check 8: no WARN for the new files).

## 4. Overlap and reuse

| New declaration | Nearest relative (`path:line`) | Relation | Why not reused |
|---|---|---|---|
| `learnerFn` | owned `learnerOf` (`Randomness/Learning.lean:96`) | restates it, with `encodeSample` unfolded through `encodeSample_eq` | helpers cannot import the owned file (it imports them), and the owned definitions are foreign to the helpers (Rule 10); the proof identifies them by `learnerOf_eq`, `encodeSample_eq` |
| `firstBit` | owned `prfConcept` (`Randomness/Learning.lean:77`) | its body (`(List.ofFn y).headD false`) as a function of the output | as above; identified by `prfConcept_eq` |
| `foldr_pairEncode_nil` | `MultiMsg.encodeHist_eq_flatMap` (`Encryption/PrivateKey/FromPRF/ReductionMachine.lean:60`) | the same fact (nested pairs ending in `[]` are a concatenation), for a fold of words instead of `encodeHist` | different fold; stated generally |
| `sampleOf` | `MultiMsg.blockMapFun` (`ReductionMachine.lean:229`) | the same block map, for `relabel` | `blockMapFun` has no published reader (lint check 8 lists it), so Rule 10 forbids unfolding it; `sampleOf` is the function of the public `Complexity.polyTimeComputable_blockMap` |
| `blk` (private) | `MultiMsg.histBlock` (`ReductionMachine.lean:50`) | the same block `⟨⟨x, y⟩, []⟩` | `histBlock` has no reader (lint check 8) |
| `sampleLen` | `MultiMsg.histBlockLen` (`ReductionMachine.lean:68`) | `m · histBlockLen` | reuses `histBlockLen` and `eval_histBlockLen` |
| `tupleWord`, `learnIn_tupleWord` | `MultiMsg.preFun_encodeHist` (`ReductionMachine.lean:433`) | the same encoded tuple shape `⟨⟨ρ_j, y_j⟩, []⟩` (with the zero mask) | different processing (relabelling, not masking) |
| `exists_learnDist` | `MultiMsg.exists_queryChain_nuppt` (`ReductionMachine.lean:461`) | a specialization (zero messages, the learner's verdict machine) | reused, not copied |
| `iid_uniform` | none found (`iid` occurs only in the PAC layer); cf. `Rejection.uniform_prod` (`Randomness/Extraction/Rejection.lean:134`) | the `m`-fold analogue of `uniform_prod` | no `iid` version exists; promotion request |
| `predictSuccess_eq_uprob` | `PAC.predictSuccess_eq_one_sub_expectedErr` (`LearningTheory/PAC/Prediction.lean`) | another reading of `predictSuccess` | the uniform-probability form is what `acceptProb` gives; promotion request (PAC layer) |
| `snocEquiv` | Mathlib `Fin.snocEquiv`; `Rejection.tupleEquiv` (`Rejection.lean:144`) | tuple splitting | the triple `(k, (s, r)), x` regrouping is specific; built from `Fin.snoc`/`Fin.init` |
| `uprob_eq_point` | `Rejection.uniform_probTrue` (`Rejection.lean:343`) | the uniform point mass, here in `uprob` form | stated directly from `uprob_eq_card_filter` |
| `uprob_flip_half`, `flipAt`, `flip0` | PRFGame collision bound `abs_expect_fImpl_sub_le` (`OracleFromPRF/Collision.lean:375`); GGM's lazy sampling | a different argument (a bit-flip involution at one fresh point, no lazy sampling) | not applicable |
| `abs_gameProb_random_sub_half_le` | `acceptProb_random_eq_lazy` (`Pseudorandom/Functions/Asymptotic/Defs.lean:128`) | random-function acceptance | the bound is direct in `uprob`; no lazy run needed |
| `zero_add_fun` (private) | Mathlib `Bool` xor lemmas | `(fun _ => false) + y = y` for the `Pi` `+` of `Bool` | one-line local fact |
| `verdictFun` | `MultiMsg.postFun` (`ReductionMachine.lean:296`) | another post-processor of a query chain | different verdict |

Nearest relatives named by the brief: ext-nosrc's sampler law (`Randomness/Extraction/Sampler.lean`:
a block law of an extractor, not reused), the GGM reduction (`GGM/Reduction.lean`: reused
`pairEncode_append_right`), the T1 reductions of hash-sign and Lamport (not used: the query chain
replaces T1), the PRFGame collision bound (above).

**Searches** (`logs/final-searches.log`): ripgrep over `TCSlib/` and Mathlib for the statement
shapes and key names of each new declaration (`foldr pairEncode`, `iid`, `uniform_prod`,
`blockMap`, `queryChain`, `snoc`, `update` with `uprob`, `headD` of `ofFn`, `label_apply`, …).

## 5. Scope requests, promotion and reader requests

**Scope requests:** none (no frozen file was edited; the route needed none).

**Promotion requests** (generic facts placed in the helpers):
- `iid_uniform` → `InformationTheory/Samples.lean` (beside `iid`).
- `predictSuccess_eq_uprob` → `LearningTheory/PAC/Prediction.lean`.
- `foldr_pairEncode_nil` → `Complexity/ClassNP/PolyTimePairing.lean` (beside `pairEncode`).
- `uprob_eq_point` → `Foundations/Probability.lean`.

**Reader requests** (missing readers met; worked around without a scope request):
`MultiMsg.histBlock`, `MultiMsg.blockMapFun` (`FromPRF/ReductionMachine.lean`) have no `_eq`
readers (lint check 8 WARN at the base); readers would let `blk` and `sampleOf` be dropped.

## 6. Checks (final)

All Lean runs one process at a time, one module per `scripts/lean_check_tree.sh` call (via
`tools/check.sh`, with start/end time, elapsed time and max RSS); the post-sweep runs are driven by
`tools/final_pipeline.sh` (step log `logs/final-pipeline.log`). No host restart during the runs.

- **Recheck and sweep** (`logs/final-sweep.log`, 01:22–01:45 UTC): the 250 modules of
  `logs/order-with-helpers.txt` (`order.txt` with the four helpers inserted before the owned
  module), each checked from scratch, in order: **250/250 status 0, no `error:`/`error(…)` line**;
  the five files of this fill emit no warning.
- **Sorry census** (`logs/final-census.txt`, `logs/final-census-vs-base.diff`): 19 declarations in
  9 modules; the diff against `base-sorries.txt` is exactly the line
  `TCSlib/Cryptography/Randomness/Learning: 1: predictAdv_prfConcept_negligible` and the total
  (20 → 19).
- **Axioms** (`logs/final-axioms.log`, `probes/AxiomsFinal.lean`): `predictAdv_prfConcept_negligible`
  and `not_weakLearnsUnder_prfConcept` depend on `[propext, Classical.choice, Quot.sound]`; the
  71 stored constants of the five files (auxiliary constants included) use exactly
  `{Classical.choice, Quot.sound, propext}`; no `sorryAx`.
- **Whole-file seals** (`seals/`; `tools/seal_gen.py`, `seal_run.py`, `seal_all.sh`). Each file is
  copied to a new module that makes every TCSlib definition of its full import closure
  irreducible and removes it from instance unfolding, abbreviations excluded; it must elaborate.
  Variants: **A** (`PolyExpr.eval` excluded as notation) and **B** (sealed), each **strict**
  (projection coercions sealed) and **coe** (projection coercions treated as notation: the one
  in the closure is `FinDist.instCoeFunForallReal`, `⟨FinDist.prob⟩`). The runner counts both
  diagnostic forms (`^\S+\.lean:\d+:\d+: error[:(]`) and keeps every raw log (`*.out`).
  - final (`final-{A,B}-{strict,coe}.jsonl`): **all five files elaborate in all four variants:
    0 errors, 0 failing declarations** (about 1,130–1,300 definitions sealed per file);
  - base (`base-{A,B}-{strict,coe}.jsonl`; the owned file is the only changed file that exists at
    the base, checked from `base/LearningBase.lean`, whose sha256 equals `SOURCE-SHA256SUMS`):
    0 errors in all four variants;
  - `seals/seals-compare.log`: no new failing declaration in any variant; strict and coe agree in
    both A and B (no difference to attribute). Why they agree: coercions are expanded at
    elaboration (`p b` is `p.prob b`), and even an explicit `CoeFun.coe inst p b` reduces under the
    strict seal, since Lean reduces a projection of an instance although the instance is
    irreducible (`probes/CoeProbe.lean`, `logs/coe-probe.log`: status `irreducible`, and the
    `isDefEq` trace unfolding `instCoeFunForallReal.1`).
  During development (not delivered) the first coe-A seal run failed once, in
  `exists_learnDist_acceptProb` (`simp only [label_apply]` made no progress on the labelled
  sample and the goal closed only by unfolding `PAC.label`); the proof now rewrites with the
  function form of `label_apply` (`hlab`).
- **Paired controls** (`controls/`, `logs/controls-plain.log`, `seals/controls-*.jsonl`):
  - `CtlUnfold` (`LearnPRF.firstBit y = … := rfl`): unsealed status 0; **1 error in each of the
    four sealed variants** (`ctl_unfold_firstBit`);
  - `CtlEval` (`(PolyExpr.const 1).eval 5 = 1 := rfl`): unsealed 0; A-strict 0, A-coe 0;
    **B-strict 1 error, B-coe 1 error** (`ctl_unfold_eval`);
  - `CtlReader` (the same facts through `firstBit_eq`, `PolyExpr.eval_const`, and `p b = p.prob b`):
    0 everywhere;
  - `CtlCoe` (an explicit application of the coercion instance by `rfl`): 0 everywhere. It was
    meant as the negative control of the strict variant and is kept as a documented probe: no
    control can make the strict variant fail on a projection coercion (see above).
  Each sealed negative fails exactly once, and the positive passes.
- **Explicit-unfold scan** (`scan/`; `tools/rwids.py`, `rwids_run.sh`, `cmp_scans.py`): every
  identifier of a `rw`/`simp`/`unfold`/… list is resolved in the file's namespaces and `open`s
  (scan modules in `scan/sources/`). Final: 179 rows: 149 theorems, 2 definitions of the scanned
  file itself (`prfConcept` in `prfConcept_decidable`, base code; `sampleLen` in `sampleLen_eval`),
  28 unresolved (local hypotheses and private declarations of the scanned file: `blk`,
  `zero_add_fun`), and **0 definitions of another TCSlib file** (`scan/scan-compare.log`); base:
  6 rows, 0 foreign.
- **Lint** (`logs/base-lint.log`, `logs/final-lint.log`, `logs/final-lint-vs-base.diff`):
  `campaign_style_lint.py TCSlib/Cryptography --check8b` gives 92 FAIL / 101 WARN at the base and at
  the final, and **the FAIL and WARN line sets are identical** (the diff is empty); no line for the
  new files.
- **Width and size** (`logs/final-width.log`): every line ≤ 100 characters, every file ≤ 1000 lines.
- **Patch reproduction** (`logs/final-repro.log`): in a scratch clone at the base, `git am` of each
  patch with the committer name, email and date of `patches/COMMITS.tsv` reproduces every commit
  hash (the author data are in the patches).

## 7. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

`evidence/SHA256SUMS` lists exactly the files under `evidence/`; the top-level `SHA256SUMS` lists
every delivered file under `inbox/fills/learning/` except itself (both checked by
`tools/manifest.sh` before the push: paths equal, hashes verified).
- `logs/`: environment and bootstrap (`preflight.log`, `source-sha256.log`, `order.txt`,
  `mathlib-roots.txt`, `cache-store.log`, `cache-get.log`, `packages-check.log`, `cache-probe.log`,
  `bootstrap.log`, `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`, `base-lint.log`);
  checkpoints (`checkpoint{1,2}-{checks,axioms,lint,width,repro}.log`); final
  (`order-with-helpers.txt`, `final-sweep.log`, `final-census.txt`, `final-census-vs-base.diff`,
  `final-axioms.log`, `final-lint.log`, `final-lint-vs-base.diff`, `final-width.log`,
  `final-searches.log`, `final-pipeline.log`, `controls-plain.log`, `coe-probe.log`,
  `scan-final.ids.log`, `scan-final.raw.log`, `scan-base.ids.log`, `scan-base.raw.log`,
  `final-repro.log`).
- `seals/`: `{final,base,controls}-{A,B}-{strict,coe}.jsonl` and `.out` (raw output),
  `seals-compare.log`, `sources/<tag>/` (every sealed copy that was checked).
- `scan/`: `scan-final.tsv`, `scan-base.tsv`, `scan-compare.log`, `sources/{final,base}/`.
- `controls/`: `CtlUnfold.lean`, `CtlEval.lean`, `CtlCoe.lean`, `CtlReader.lean`.
- `base/`: `LearningBase.lean` (the owned file at the base).
- `probes/`: `CacheProbe.lean`, `AxiomsCP1.lean`, `AxiomsCP2.lean`, `AxiomsFinal.lean`,
  `CoeProbe.lean`.
- `tools/`: every script used (`check.sh`, `dev.sh`, `mk.py`, `sweep_chunk.sh`, `census.py`,
  `cmpcensus.sh`, `pkgcheck.py`, `seal_gen.py`, `seal_run.py`, `seal_all.sh`, `rwids.py`,
  `rwids_run.sh`, `cmp_scans.py`, `width_check.py`, `final_pipeline.sh`, `payload.sh`,
  `repro_check.sh`, `manifest.sh`, `finalize.sh`).

`patches/`: `git format-patch 107f1e8c..f30d80f02` (3 patches) and `COMMITS.tsv`; `src/`: the five
changed and new files at `f30d80f02`.

## 8. From the checkpoints

### 8.1 Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the headroom
  is `MemAvailable` = 16489095168 B = 15.36 GiB; the clone's filesystem (ext4, `/dev/vda`) has
  18171547648 B = 16.92 GiB free (floor 12 GiB): `PREFLIGHT PASS`. Before the preflight the disk had
  9.87 GiB free (below the floor); with the user's approval in the session, the two git worktrees
  of this host's finished, delivered fills (`/workspace/dlc`, `/workspace/ett`) were removed
  (`git worktree remove`; their branches are kept). No dependency tree was copied or moved.
- **Clone:** a new worktree `/workspace/learn` of the local repository, branch `fill/learning` at
  the issue base. Its source files match `SOURCE-SHA256SUMS` (246 files, `source-sha256.log`).
- **Cache:** the store (`~/.cache/mathlib`, `cache-store.log`) already held 2402 archives, left by
  this host's earlier fills. The narrowed `lake exe cache get` for the 82 roots
  (`mathlib-roots.txt`, the same list as the pack's `roots.txt`) cloned the packages of the
  manifest, printed "No files to download" and "Decompressing 2125 file(s)", and exited 0
  (`cache-get.log`). No zero-size olean. The probe importing `Mathlib.Algebra.BigOperators.Field`
  elaborates (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports them).
- **Bootstrap** (`bootstrap.log`): the 246 modules of `order.txt`, one `scripts/lean_check_tree.sh`
  call each (through `tools/check.sh`, with start/end time and max RSS), in order: 246/246 status 0,
  no error. No host restart. Sorry census = `base-sorries.txt` (20 declarations in 10 modules;
  `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`: identical).

### 8.2 Step 1 (checkpoint 1)

New helper modules (namespace `TCSlib.Cryptography.Randomness.LearnPRF`):

| File | Lines | Role |
|---|---|---|
| `Randomness/Learning/Sample.lean` | 259 | the learner's input and the last label, as polynomial-time functions of the encoded tuple |
| `Randomness/Learning/Distinguisher.lean` | 136 | the distinguisher `exists_learnDist` |
| `Randomness/Learning/Law.lean` | 173 | the game probability; prediction game and acceptance probability |

The owned file imports the three modules (and nothing else changes in it at this checkpoint).

- **The distinguisher** (`exists_learnDist`): for a learner machine `A` and a polynomial `m`, a
  next-query machine `B` whose coins at `n` are, by a bijection `φ`, `m(n) + 1` points `ρ` and
  `A`'s coins `c`, and whose tree with budget `m(n) + 1` against any oracle `g` evaluates to
  `decide (A(⟨S, ⟦ρ_m⟧⟩; c) = [true]) == firstBit (g ρ_m)`, with `S` the nested labelled examples
  `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩` of the first `m(n)` points. It is the public query chain
  `MultiMsg.exists_queryChain_nuppt` (non-adaptive queries at points from the coins, here with the
  zero message vector) of the machine `C` that runs `A` on `learnIn m` (`NUPPT.exists_compParam`)
  and compares with `lastLabel m` (`NUPPT.exists_seq` with the uniform machine of `verdictFun`).
  So no T1/T2/T4 run is needed: the query chain already gives a next-query machine
  (`toOracleAdversary`) at `ℓ₁ = ℓ₂ = n`.
- **The learner's input** (`learnIn_tupleWord`, `lastLabel_tupleWord`): the encoded tuple is the
  concatenation of `m(n) + 1` blocks of `6n + 6` bits; a fold of pairs ending in `[]` is a
  concatenation (`foldr_pairEncode_nil`), so the labelled sample is the block map of `relabel` over
  the first `m(n)` blocks (`MultiMsg.flatMap_range_blocks`), polynomial-time by
  `Complexity.polyTimeComputable_blockMap`, `polyTimeComputable_pairTakePoly`/`DropPoly`.
- **The law** (`exists_learnDist_acceptProb`, `predictSuccess_eq_uprob`): for every keyed family
  `G : K → {0,1}^n → {0,1}^n`, `acceptProb G (oracleDist (B.toOracleAdversary n n n (m(n)+1)))` is
  `gameProb (m n) G (learnerFn A n (m n))`, the uniform probability over `((k, (s, r)), x)` of
  `learnerFn … (label (firstBit ∘ G k) s) r x == firstBit (G k x)`; the coins are relabelled by
  `φ` and `snocEquiv` (examples, then the fresh point). The prediction game is the same uniform
  probability: its law is a product of uniform laws (`iid_uniform`, `Rejection.uniform_prod`,
  `Rejection.uniform_probTrue`). The final step identifies `learnerFn` with the owned `learnerOf`
  (`learnerOf_eq`, `encodeSample_eq`) and `firstBit ∘ F n k` with `prfConcept F n k`
  (`prfConcept_eq`), giving `predictSuccess (prfConcept F n) m (learnerOf A n m) = acceptProb (F n) D`.

**Edge cases of step 1.** `n = 0`: all statements hold (one point, `firstBit` is `false`).
`m(n) = 0`: the sample is empty (`List.ofFn` over `Fin 0`), the tuple is the single last block.
A fresh point equal to an example: no case distinction, the uniform probabilities range over all
tuples. `A` printing anything other than `[true]`: `learnerFn` is `decide (… = [true])`, as
`learnerOf`. The coins: `B`'s coins are, by `φ`, the `(m(n) + 1)` points (`(m(n)+1)·n` bits, in
`n`-bit blocks) and `A`'s coins (`C`'s coins are `A.coins + 0`, relabelled by `finCongr`).

### 8.3 Step 2 (checkpoint 2)

New helper `Randomness/Learning/Random.lean` (203 lines), imported by the owned file:
`abs_gameProb_random_sub_half_le`: for `n ≥ 1`, every learner `ℓ` and `m` examples,
`|gameProb m (fun R => R) ℓ − ½| ≤ m / 2^n`, the game with a uniform random function
`R : {0,1}^n → {0,1}^n` in place of the keyed family (with step 1, `acceptProb (randomFunction …) D`
is this game, `randomFunction_apply`).

- Put `R` last and average over it first (`uprob_comp_equiv`, `uprob_prod`). For fixed examples
  `s`, coins `r` and fresh point `x`:
  - if `x` is none of the examples, `flipAt hn x R = update R x (flip0 (R x))` (flip the first bit
    of `R x`) is an involution of the functions (`flipAt_involutive`) that keeps the labels of the
    examples (`Function.update_of_ne`) and negates the label of `x` (`firstBit_flip0`); it maps the
    winning functions onto the losing ones, so the probability is exactly `½` (`uprob_flip_half`,
    `uprob_comp_equiv`, `uprob_not`);
  - otherwise the probability is in `[0, 1]`.
- So `|gameProb − ½| ≤ Pr[∃ j, s_j = x]` (the average of `|p − ½| ≤ [x ∈ s]`), and the union bound
  (`uprob_exists_le`) with `Pr[s_j = x] = 2^{-n}` (`uprob_prod`, `uprob_eq_point`) gives `m / 2^n`.
- `n ≥ 1` is needed for the first bit; at `n = 0` the final step uses an eventual bound.

New declarations: `flip0` (`flip0_eq`, `flip0_flip0`), `firstBit_of_pos`, `firstBit_flip0`,
`flipAt` (`flipAt_eq`, `flipAt_involutive`), `uprob_flip_half`, `uprob_eq_point`,
`abs_gameProb_random_sub_half_le`.

Overlap (step 2): the flip argument has no TCSlib relative (searched `update`/`involutive`/`flip`
with `uprob` in `TCSlib/Cryptography`); `uprob_eq_point` (`Pr[x = y] = 1/2^n`) is the uniform
point mass, which `Rejection.uniform_probTrue` would give through `FinDist`; the `uprob` form is
stated directly from `uprob_eq_card_filter`. The PRFGame collision bound
(`OracleFromPRF/Collision.lean:375`, `abs_expect_fImpl_sub_le`) bounds the repetition of a nonce
in the CPA game (lazy sampling, `q²/2ⁿ`); here the bad event is one fixed point among `m` samples,
bounded directly.

Evidence added: `logs/checkpoint2-checks.log` (status 0; the one `sorry` warning is the target),
`checkpoint2-axioms.log` (`propext`, `Classical.choice`, `Quot.sound`), `checkpoint2-lint.log`
(92 FAIL / 101 WARN, the base's line sets), `checkpoint2-width.log`, `checkpoint2-repro.log`
(both hashes reproduced), `probes/AxiomsCP2.lean`.

