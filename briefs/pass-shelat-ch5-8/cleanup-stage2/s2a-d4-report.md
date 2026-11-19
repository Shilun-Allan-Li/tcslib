# Cleanup Stage 2, S2-A batch D4 (Seyoon's rulings of 2026-11-18): report

**Status:** D4 is done in-house.
- **Code:** the four ruled items are committed, one signed commit each, and pushed fast-forward to
  `cleanup/stage2-s2a`. The head is **`9f7f409c2e09749428db75b9ddd324f92695e4af`**.
- **Replay:** clean.
- **Seals:** coe-A and coe-B give 0 errors on all 10 S2-A owners checked, now including `SamplingFinDist` and
  `CollisionOutput`. `FromPermutation` keeps job J3's residue, identical to D3's.
- **S2-A rows:** every row is done. The only size findings left are the ones assigned to Stage 3.
- **Interruptions:** the replay was interrupted twice and resumed both times (§2):
  - a container restart killed it;
  - then its disk guard stopped it below 1.5 GB free;
  - the coordinator freed disk (Q-D4-1 (a)).

Evidence is in `$SP/s2a-d4/`, where `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
Its `SHA256SUMS` file covers 544 files and has SHA-256
`51d39684348f257592ed45b56c8f745c92e36a84b56585e2c164b7a8def06b30`.

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
| Development seals (records of D2's or D3's head) | `SamplingFinDist` A/B 0/0 (1/1 at D3); `HardCore/Functions` 0/0; `CollisionOutput` A/B 0/0 (1/1 at D3) |
| decls2 vs D3 head | ADDED `epsClose_iff`, `rawCollisionInputs_fst`, `rawCollisionInputs_snd` (the last two existed before as generated lemmas; decls2 does not see `simps!` output; same names and statements); nothing CHANGED or REMOVED. The private `invProbAt_glPad_eq` is not tracked |
| decls2 vs base `61a5f0fb` | 41 ADDED, 15 CHANGED, 4 REMOVED: D3's list plus those 3 ADDED, all ruled |
| Admissions (`sorryscan.py`) | `TOTAL 192 in 44 modules; native_decide 0; axiom 0`, byte-identical to D3 |
| `style_lint` on the 9 files | 2 findings, both size: `Collections` (1,177 lines, already over at the base) and `Factoring` (1,924, Stage 3, Q-D3-2 (A)). The 5 sketch findings and `OneWayYao`'s size finding are gone. `OneWay` is not touched; its size finding stays for Stage 3 |
| `campaign_style_lint --check8b` | FAIL 25/92 unchanged; WARN Complexity 389 unchanged, Cryptography 105 → 104 (`OneWayYao` size WARN gone) |

**The D4 replay** ran on `$SP/olean-replay-s2a-d4`, a `cp -al` copy of D3's tree, which was kept intact as the parent.

| Check | Result |
|---|---|
| Plan | from D3's checked state at `9f7f409c`: 9 changed modules, 288 to build, 1,159 reused |
| Runs | 3. The first was killed by the container restart after 77 modules, during `EncryptThenTag/CPAHandler`. The second was stopped by the runner's disk guard after 84. The third ran the last 204 (`queue-resume2.txt`) |
| Resume rule | before each resume, every completed module's `.olean` was checked against its run record (all matched), and every module without a completed record (`CPAHandler` among them) was rebuilt |
| `permod` | 288 modules; rc≠0 0; `error:` 0; `error(` 0; `sorry` 0; no log/record mismatches |
| `stateplan update`, then `check` over the 1,447-module order | 288 taken; **RESULT OK** |
| Link counts | 288 rebuilt at link count 1; 1,159 reused, all hard links |
| Output map | 1,478 entries, SHA-256 `1abe4bed0742baa2495c4f193b9c70192ac8aaca121fc8c10761027795b2692d` |
| Output map vs D3's map | changed only the 9 changed modules |
| `NthRootLemmas` overlay | `c0a9cff0…` |
| D3 tree rehash | byte-identical map before, after the copy, after the restart, after the disk stop, before the last resume, after the replay and at the end |
| D4 tree rehash | byte-identical map after the seals |

**Seals at the head** (`seal/d4/`, D4 tree, the archived instrumenter unmodified, gated runner):
- **Owners:** 11 — the 9 changed modules, plus `HardCorePermutation/GoldreichLevin` and
  `Generators/Asymptotic/FromPermutation` downstream.
- **Probes run:** 20, because 2 B probes are byte-identical to their A probe (`order/ab-dedup.tsv`).

| Owner | coe-A D3 → D4 | coe-B D3 → D4 |
|---|---|---|
| `Asymptotic/SamplingFinDist` | 1 → **0** | 1 → **0** (= A) |
| `Hashing/SIS/CollisionOutput` | 1 → **0** | 1 → **0** |
| `InformationTheory/Extractors` | (not sealed before) → 0 | (= A) 0 |
| `Collections`, `EnsemblesLemmas`, `HardCoreLemmas`, `OneWayYao`, `Factoring`, `HardCore/Functions`, `GoldreichLevin` | 0 → 0 | 0 → 0 |
| `Generators/Asymptotic/FromPermutation` | 2 → 2 | 19 → 19 |

- **The `FromPermutation` residue is job J3's**, and unchanged:
  - it is the same declarations as at D3 (`exists_owpPredictorSnoc`; with B, also `iterPRG`, `iterPRG_eq_expand`,
    `cor_81_7`, `owpGenPRG*` and `owp_hardcore_prg`), which are scope rows S2-SL-313..315 and S2-BO-002/009/155..163;
  - the error lines are identical to D3's, line for line.

## 3. Deviations

- **Item 3, placement:** the lemma sits after the four `glPad` string lemmas, not directly beside `glPad_inEquiv_ofFn`,
  because it uses all four.
- **Item 4, option:** explicit lemmas, for the reason given in §1.
- **Item 2, trim size:** `OneWayYao` was trimmed to 999 lines. `style_lint` counts one line more than `wc`, so this is the
  most it can have and pass.

## 4. Items left

None in S2-A. S2-SL-214 is complete (item 1). The remaining size findings belong to Stage 3:
- `OneWay`, `Factoring` and the other files already over 1,000 lines;
- `Collections` (1,177), already over at the base.

The `invProbAt_glPad_eq` lemma (item 3) and the two explicit field lemmas (item 4) are the ruled additions.

**Ready to run** — S2-A D4 is complete at `9f7f409c`; the replay output `$SP/olean-replay-s2a-d4` is kept for adoption.
