# Cleanup Stage 2, S2-A batch D4 (Seyoon's rulings of 2026-11-18): report (interim)

**Status:** the code is finished, but the checks are not.
- **Code:** all four items are committed, one signed commit each, and pushed fast-forward to `cleanup/stage2-s2a`.
  The head is **`9f7f409c2e09749428db75b9ddd324f92695e4af`**.
- **Done at the head:** the development seals, decls2, the admissions and the lints.
- **Not done:** the D4 replay is at 84 of 288 modules, and the final seals have not been run.
- **First stop:** a container restart killed the replay.
- **Second stop:** I resumed it, and the runner's disk guard stopped it when free space fell to about 1.4 GB. Other jobs'
  directories were filling the disk. Under the 2,000 MB rule I stopped there. My own scratch has nothing large enough to
  free, because the D1 and D2 evidence stay.
- **Resume:** run the queue file `replay/plan/queue-resume2.txt` (204 modules) once free space is above 2,000 MB.

Evidence is in `$SP/s2a-d4/`, where `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

| Pin | Value |
|---|---|
| D3 head (D4 start) | `dff281b53746377cd72e57c3aeeadf3d1f59a332` |
| Branch head | **`9f7f409c2e09749428db75b9ddd324f92695e4af`** (`origin/cleanup/stage2-s2a`; draft PR #390) |
| Rulings | decision-log rows of 2026-11-18, records tip `75c2fc7a` |

## 1. Commits (`git commit -S`, explicit paths, the two trailer lines; all four carry an SSH `gpgsig` header)

| Item | Commit | Files |
|---|---|---|
| Q-D2-1 (A): `epsClose_iff`; S2-SL-214 finished | `27cbdeb057f915e64be8fe42790f2f965c5ee219` | `InformationTheory/Extractors` +5, `Asymptotic/SamplingFinDist` +2 −1 |
| Q-D2-3, Q-D3-1 (A): five proof sketches; `OneWayYao` under 1,000 lines | `d6fd4bb5bcb033e8a8ada44cc1cf03d52a91af05` | `Collections`, `EnsemblesLemmas`, `HardCoreLemmas`, `OneWayYao`, `Candidates/Factoring` (+56 −36, docstrings only) |
| Q-D2-4 (A): the private `invProbAt_glPad_eq` | `96918135065b801d67d1be953fef4ea6e222eb1c` | `HardCore/Functions` (+35 −48 before wrapping) |
| Q-D2-5 (B): explicit field lemmas in place of `simps!` | `9f7f409c2e09749428db75b9ddd324f92695e4af` | `Hashing/SIS/CollisionOutput` +22 −1 |

**Item 1: Q-D2-1.**
- **New reader:** `InformationTheory.epsClose_iff : EpsClose ε p q ↔ ∀ D, |p.probTrue D - q.probTrue D| ≤ ε := Iff.rfl`.
  It sits beside `EpsClose` and carries the source tag [PS10, Def 181.1].
- **S2-SL-214:** `statClose_iff_epsClose_map` now introduces `EpsClose` through it (`refine epsClose_iff.2 fun D => …`).
  The row is complete.

**Item 2: Q-D2-3 and Q-D3-1.**
- **Proof sketches** are added to `toCollection_sampleClose`, `acceptProb_multicopyRed_congr`, `owpPredMachine_predProb`,
  `statClose_sampleAll` and `fac_prodInverter_eq_yaoB`.
- **`OneWayYao.lean`** is now 999 lines. Three docstrings were tightened: the module overview, the loop identity and
  `exists_yaoReduction`.
- **Docstrings only:** with comments stripped, the code of all five files is identical to D3's.
- **No splits:** no declaration moved. The `OneWay` and `Factoring` splits stay with Stage 3.

**Item 3: Q-D2-4.**
- **New lemma:** the private `FunFamily.invProbAt_glPad_eq`. It sits after the four `glPad` string lemmas
  (`glPad_inEquiv_ofFn`, …), because its proof uses all four. It has a docstring, the tag [PS10, Theorem 87.3] and a
  proof sketch.
- **Proof:** it is the former `hbridge`, unchanged.
- **Uses:** `StrongOneWay.glPad` and `StrongOneWay.glPad_hardCore` both use it. No copy of `hbridge` is left.
- **Amend:** the commit was amended once before the push, to wrap two lines that had become longer than 100 characters.

**Item 4: Q-D2-5, option chosen: explicit field lemmas.**
- **What changed:** `@[simps! (config := { isSimp := false }) fst snd]` is removed. The two lemmas it generated are now
  written out with the same names and statements, and still without `@[simp]`:
  - `rawCollisionInputs_fst m raw a : (rawCollisionInputs m raw).1 a = padFin (m + m) raw (Fin.castAdd m a)`;
  - `rawCollisionInputs_snd m raw a : (rawCollisionInputs m raw).2 a = padFin (m + m) raw (a.addNat m)`.
- **Proofs:** they read bit `a` of the published `ofFn_splitCoins_fst` and `ofFn_splitCoins_snd`. No `splitCoins` reader
  is added.
- **Why not a reader:** `simps!` unfolds the definition body itself, so a reader beside `splitCoins` would not have fixed
  the attribute under seal.
- **Same statements:** on D3's tree, the generated types equal the written statements at reducible transparency
  (`q5/SimpsEq.lean.txt`, rc 0).
- **What is lost:** the old lemmas were `rfl` lemmas, usable by `dsimp`. Nothing in the library uses either name.
- **Import:** `import Mathlib.Tactic.Simps.Basic` stays, so the import graph is unchanged.

## 2. Checks

| Check | Result |
|---|---|
| Per-item file checks (`lean_check_tree.sh` on a `cp -al` of D3's tree, since deleted) | all changed files, plus the direct importers of `Extractors` (2), `HardCore/Functions` (3) and `CollisionOutput` (2): rc 0, 0 errors, no `sorry` |
| Development seals (records of D2's or D3's head) | `SamplingFinDist` A/B **0/0** (1/1 at D3); `HardCore/Functions` 0/0; `CollisionOutput` A/B **0/0** (1/1 at D3) |
| decls2 vs D3 head | ADDED `epsClose_iff`, `rawCollisionInputs_fst`, `rawCollisionInputs_snd` (the last two existed before as generated lemmas; decls2 does not see `simps!` output); nothing CHANGED or REMOVED. The private `invProbAt_glPad_eq` is not tracked |
| decls2 vs base `61a5f0fb` | 41 ADDED, 15 CHANGED, 4 REMOVED: D3's list plus those 3 ADDED |
| Admissions (`sorryscan.py`) | `TOTAL 192 in 44 modules; native_decide 0; axiom 0`, byte-identical to D3 |
| `style_lint` on the 9 files | 2 findings, both size: `Collections` (1,177 lines, already over at the base) and `Factoring` (1,924, Stage 3). The 5 sketch findings and `OneWayYao`'s size finding are gone |
| `campaign_style_lint --check8b` | FAIL 25/92 unchanged; WARN Complexity 389 unchanged, Cryptography 105 → 104 (`OneWayYao` size WARN gone) |
| D3 tree rehash (`$SP/olean-replay-s2a-d3`) | byte-identical map before, after the copy, after the restart and after the stop |
| **D4 replay** | **incomplete**; details below |

**The D4 replay:**
- **Setup:** `$SP/olean-replay-s2a-d4` is a `cp -al` copy of D3's tree. The plan, made from D3's checked state, lists 9
  changed modules: 288 to build and 1,159 reused.
- **Progress:** 84 modules are built, all rc 0 with 0 errors. Each built `.olean` matches its run record.
- **Interruptions:** the run was killed once by the container restart, during `EncryptThenTag/CPAHandler`. That module
  is rebuilt in the resumed run. The run was then stopped once by its disk guard.
- **Left:** 204 modules, listed in `replay/plan/queue-resume2.txt`. Every module not yet built keeps D3's object, and the
  resume rebuilds each of them.

**Still to run once disk allows:**
- the rest of the replay;
- `permod`, then `stateplan update`/`check`, the link counts and the output map;
- the final coe-A/coe-B seals on the touched owners and `FromPermutation`, where J3's residue is expected unchanged;
- the D3 rehash at the end.

## 3. Deviations

- **Item 3, placement:** the lemma sits after the four `glPad` string lemmas, not directly beside `glPad_inEquiv_ofFn`,
  because it uses all four.
- **Item 4, option:** explicit lemmas, for the reason given in §1.
- **Item 2, trim size:** `OneWayYao` was trimmed to 999 lines. `style_lint` counts one line more than `wc`, so this is the
  most it can have and pass.

## 4. Questions

- **Q-D4-1. Disk for the rest of the replay** (about 0.2–0.4 GB of new objects).
  - **(a) Recommended:** free space to above 2,000 MB (other jobs' scratch), then I resume from
    `queue-resume2.txt`, followed by the acceptance checks and the seals.
  - (b) Allow me to delete my D1/D2 evidence seal logs (`$SP/s2a-d2/seal`, 574 MB) after archiving their `SHA256SUMS`.

**Not yet clear to merge — the D4 replay (204 modules) and the final seals are pending: disk below 2,000 MB.**
