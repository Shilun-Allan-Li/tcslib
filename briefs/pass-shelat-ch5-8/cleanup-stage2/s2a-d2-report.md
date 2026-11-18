# Cleanup Stage 2, S2-A batch D2 (steps A19–A38): report

**Status:** D2 is done in-house, except for two steps.
- **On the branch:** `cleanup/stage2-s2a` has 19 new signed commits, one per plan step. The branch is pushed to origin
  (fast-forward from D1's head). No PR is open and nothing is merged.
- **Steps:** 18 of the 20 steps are done. A30 is partial. A37 is not done, and gets no commit.
- **TSV rows:** of the 260 D2 rows (`items-d2.tsv`):
  - 242 are done;
  - 1 is partly done (S2-SL-214, EpsClose residue);
  - 1 is the records edit S2A-N03;
  - **16 are left** (A30: 9 rows; A37: 7 rows).
- **Checks:** the D2 replay is clean (345 modules rc 0, 0 errors; state check OK over 1,447). Admissions are unchanged.
  decls2 matches the rulings. The 12 changed definition bodies are `rfl`-equal to their D1 bodies.
- **Seals:** coe-A and coe-B give 0 on 36 of the 40 owners at the head. The 4 residues are:
  - the open items A30 and A37;
  - one `EpsClose` read;
  - one `@[simps!]` failure that predates S2-A.
- **Lint:** it shows new findings in files D2 touched (§2, Q-D2-3).

Evidence is in the session scratchpad, `$SP/s2a-d2/`, where `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`. Its `SHA256SUMS` file has SHA-256
`7d0ecfdacda5865d848d501ca02238e639c7a2466e0a72077bdafc0930e299bd` (1,650 files).

| Pin | Value |
|---|---|
| Base (records tip, S2-A base) | `61a5f0fb640622c15fdd33df56efa470b2bf26c8`, Lean-equal to snapshot #10's T `cf6a2266` |
| D1 head (D2 start) | `c119a3c4f1d8642b1328740f1d1d1165a92f5567` |
| Branch head | **`a1545eae990f82918ad4e344428e38668ab911ed`** (`origin/cleanup/stage2-s2a`) |
| Worktree | `$SP/wt-s2a` (sparse, as in D1) |
| Inputs | `s2a-workplan-r1.md`, `s2a-items.tsv`, D1's report, and `cleanup-stages.md` "Stage 2 rulings" and "S2-A rulings Q-A1 to Q-A11" |

## 1. Commits (one per step, all `git commit -S`, staged by explicit path)

| Step | Commit | Files (+/−) |
|---|---|---|
| A19 NumberTheory, InformationTheory, SamplingFinDist | `75b04bd0a71e44f092bb3fad3ceb03f60fa8fba8` | `SamplingFinDist` +8 −5, `Chebyshev` +4 −2, `Primality` +17 −8, `Entropy` +4 −4, `LeftoverHash` +3 −3 |
| A20 InnerProduct reader, GoldreichLevinDomain, Hashing re-points, PS10 A8 | `f9c03bbe6ef08bc52147bd138abb8faad2fb9056` | `GoldreichLevinDomain` +5 −3, `BooleanVector` +3 −3, `InnerProduct` +6 −3, `CollisionResistant` +4 −3, `FromDiscreteLog` +4 −5, `FromDiscreteLog/Encoding` +4 −15, `/Probability` +3 −2, `SIS/CollisionOutput` +7 −5 |
| A21 CollectionsHelpers, EnsemblesLemmas (DL-35 #1/#3) | `dd0473643756b251518a3e8585e2d95a38ff66b1` | `CollectionsHelpers` +1 −2, `EnsemblesLemmas` +52 −45 |
| A22 OneWayYao readers and fixes | `061c4e97d441b8863535fa17bc48e9823c94f0c0` | `OneWayYao` +47 −19 |
| A23 OneWay part 1 (readers, bodies) | `69660020bec9df2fca95eb6e9095d90f5317577e` | `OneWay` +40 −12 |
| A24 OneWay part 2 (four headers) | `75f85d89594e505d4f5cba57828afbf5f4eaf1d3` | `OneWay` +120 −49 |
| A25 Ensembles copies body and `copies_X` | `817f2b54efc8c06a50c03a8f2db1f6f9c59ecc8a` | `Ensembles` +23 −15 |
| A26 Ensembles seal fixes | `e8d81c5db11486be83f4a46cafbd51c876f08c9e` | `Ensembles` +28 −17 |
| A27 UniversalLemmas, UniversalPadding, BlockEncryptor | `18d7a5d68d5cf3b808867f60f69fdb6b6905072e` | `BlockEncryptor` +6 −8, `UniversalLemmas` +7 −3, `UniversalPadding` +24 −9 |
| A28 Collections, Concrete | `fc676daaa165d64caac253cd91666bd6d4fa8e4f` | `Collections` +74 −28, `Concrete` +3 −7 |
| A29 Universal | `64d662b3371aa47cc175c9cedbb6d78dae1e9bbe` | `Universal` +37 −16 |
| A30 Factoring (**partial**) | `ecd35ee997a6aa4147e4eada2a12560e61821a0b` | `Factoring` +16 −22 |
| A31 RSA, Rabin, DDH, DyadicUniform (Q-A7 b) | `f68d452534359bf27622fcb5add2658700884bd2` | `DDH` +6 −19, `RSA` +5 −3, `Rabin` +8 −3, `DyadicUniform` +16 −50 |
| A32 HardCoreLemmas, HardCoreLoops | `dbd03dea6851597223d0f38edc4ce42b2745be58` | `HardCoreLemmas` +19 −8, `HardCoreLoops` +7 −3 |
| A33 HardCoreGL, GLColl, GLFamily | `a0e600206bebb76ce66a49ab4fd039295b978ad7` | `HardCoreGL` +20 −7, `HardCoreGLColl` +6 −3, `HardCoreGLFamily` +7 −4 |
| A34 HardCoreCollection | `88d52800ae54c013ab7dcc31a948df2423a8464a` | `HardCoreCollection` +17 −10 |
| A35 HardCore/Functions part 1 (bodies, Q-A3) | `44f8909ac9df1e9023e30e6c4fa7c8e96050615e` | `HardCore/Functions` +117 −37 |
| A36 HardCore/Functions part 2 | `54fb99bf8761fa7e3d9cf9f8a2676b5948115c77` | `HardCore/Functions` +12 −7 |
| A37 GoldreichLevin (`oddCoins`) | **not done, no commit** | — |
| A38 Relational docstrings (G49-01/02), Q-D1-1 labels | `a1545eae990f82918ad4e344428e38668ab911ed` | `Games/Relational` +15 −5, `SeedMajority/Enumeration` +1 −1, `/State` +1 −1 |

- **Size:** 39 modules changed, +806 / −473 lines from D1's head; 61 modules, +1,341 / −762 from the S2-A base.
- **Messages:** each is `S2-A <step>: <summary>`, lists its rows, and ends with the two required trailer lines.
- **Signatures:** all 19 commits carry an SSH `gpgsig` header. `git verify-commit` cannot check them here, because
  `gpg.ssh.allowedSignersFile` is not configured. This is the same as D1.
- **Records** (main checkout, not this branch):
  - the DL-62 row in `duplication-ledger.md` (Q-D1-3 a);
  - the dated correction S2A-N03 in `briefs/pairings/fills/bb1-sim/design-r1.md` §2.2.
  
  The coordinator committed both in `4f3ac57f0`. Their text is unchanged since.

## 2. Checks

**Per-step file checks** (`scripts/lean_check_tree.sh`, one Lean process at a time, on a `cp -al` working tree of
D1's replay output, since deleted):
- **What was checked:**
  - every changed file of every step;
  - the direct importers of each statement-visible change:
    - A21: 26 of its 28 (`Ensembles` and `Collections` in their own steps);
    - A24: all 11 except `Collections` and `Universal`, which are in A28/A29;
    - A26: its 3, in `checks/A26`;
    - A28: 10 of its 11 (`HardCore/Functions` in A35);
    - A29: `Universal`'s importer;
    - A35/A36: `HardCorePermutation/GoldreichLevin` (`checks/A37pre`). The facades are covered by the replay.
- **Result:** at commit time, all rc 0, 0 errors, and no new `sorry`. Logs: `checks/<step>/`, `checks-*.out`.
- **Superseded:** the replay below rebuilds all of these.

**Development seals:** coe-A and coe-B probes of each step's owners before committing (`devruns/`, `seal/d2dev/`).
- **Harness lines:** they ran against D1-head seal records, so some probes print "probeNN:0" harness lines for names
  the records list. These lines are not source errors.

**D2 replay** (`replay/`):
- **Setup:** the recipe of `snapshots.md`, on `$SP/olean-replay-s2a-d2`, a `cp -al` copy of D1's replay output
  (Q-D1-2 a).
  - **Plan:** `stateplan` from D1's checked state, with `downorder` and `fullorder` at `a1545eae`.
  - **Queue:** **345 to build**, 1,102 reused. By state revision, 323 build at `c119a3c4` and 22 at `cf6a2266`.
  - **Runner:** the recipe's runner, unmodified, one module per call, slot-gated.
- **Results:**

  | Check | Result |
  |---|---|
  | `permod` | 345 modules; rc≠0 0; `error:` 0; `error(` 0; log/record mismatches none |
  | `sorry` warnings | 0. None of the 44 admitted modules is downstream of D2 |
  | `stateplan update`, then `check` over the 1,447-module full order | 345 taken; **RESULT OK** |
  | Link counts | 345 rebuilt `.olean` at link count 1; 1,102 reused, all hard links |
  | Output map (`mapnoml.py`, no Mathlib) | 1,478 entries, SHA-256 `524b504fb65baf7eec9c306c1cb43e0366b68a149b58f9335c16b2a12507255f` |
  | Output map vs D1's map | 1,438 equal and 40 changed (the 39 changed modules and `HardCorePermutation/GoldreichLevin`); none added or removed |
  | `NthRootLemmas` overlay | `c0a9cff0…` |
  | Snapshot #10 rehash (`$SP/olean-snapshot-10`, map `84d88738…`) | 0/0/0 before, after the replay and at the end |
  | D1 replay tree rehash (D1 map `216f8131…`) | byte-identical map before, after the replay and at the end |

- **Rehash script:** `rehash.sh` was re-pointed to `$SP/olean-snapshot-10` after the #11 adoption, as the coordinator
  asked (`log/notes.txt`). `rehash-before` ran at 07:52Z, when `$SP/olean-snapshot` was still #10.

**Admissions** (`admissions/`, `sorryscan.py` over the full order): the base, D1's head and D2's head all give
`TOTAL 192 in 44 modules; native_decide 0; axiom 0`. The three files are byte-identical.

**Q-A2 (a) `rfl` probes** (`qa2/`):
- **Method:** `QA2.lean` copies each changed body as it stood at D1's head, verbatim, under the suffix `_d1`. The only
  change is that `Ensembles`' private alias `blocks` is written `FunFamily.blocks`, which it is by `rfl`. The probe then
  states `new = old := rfl` for each, unsealed, on the replay output.
- **Result:** **12/12 pass** (rc 0, no messages):
  - `FunFamily.prod`;
  - `PermFamily.toFunFamily`, `toFunFamily_domEquiv`, `toFunFamily_codEquiv`;
  - `Ensemble.copies`;
  - `Collection.owfFamily`;
  - `Collection.glPad` (whole structure, with the D1 proof of `sample_spec`);
  - `FunFamily.glPad`, `glBit`, `glInverter`, `glPad_inEquiv`, `glPad_outEquiv`.
- **Control:** `QA2Ctl.lean` negates `glBit` and composes `toFunFamily_domEquiv` with Boolean negation. Both fail
  (Type mismatch), so the probe is not vacuous.
- **Not probed:** the other 3 ruled bodies (`fmult`, `plantFactor`, `oddCoins`) are unchanged (A30 rest, A37).

**Seals at the head** (`seal/d2/`):
- **Setup:**
  - **Collector and instrumenter:** a collector over **40 owners** (the 38 D2 code owners, including the untouched
    consumer `HardCorePermutation/GoldreichLevin`, plus `SeedMajority/Enumeration` and `/State`). Then canonical
    **coe-A** and **coe-B** with the archived Gate 06/10 instrumenter, unmodified.
  - **Tree and runner:** the D2 replay output, through the gated runner (`lean -DmaxErrors=0`, no `-o`).
  - **Deduplication:** 8 B probes are byte-identical to their A probe (normalized label), so 72 probes ran
    (`order/ab-dedup.tsv`).
- **Base comparison** (`seal/base/`):
  - **Tree:** the same 38 code owners at `61a5f0fb`, on a temporary `cp -al` copy of snapshot #10 with the overlay
    (since deleted); 69 probes after deduplication.
  - **SeedMajority:** its base values are D1's (0/0).
  - **Interrupted run:** the base run was stopped once by the 2-hour background limit and resumed on the remaining list
    (`seal-runs2`, `seal-runs3`, `log/notes.txt`). The interrupted probe was re-run from the start.
- **Table:** `seal/table.tsv`, with errors per probe.

| Owner | coe-A base → head | coe-B base → head |
|---|---|---|
| `Ensembles`, `EnsemblesLemmas` | 12, 11 → **0** | 16, 11 → **0** |
| `OneWay`, `OneWayYao` | 0, 10 → **0** | 32, 11 → **0** |
| `HardCore/Functions`, `HardCoreCollection` | 6, 8 → **0** | 29, 9 → **0** |
| `HardCoreGL`, `HardCoreLemmas`, `GLColl`, `GLFamily`, `HardCoreLoops` | 4, 1, 0, 0, 0 → **0** | 5, 9, 3, 3, 0 → **0** |
| `Universal`, `UniversalLemmas`, `UniversalPadding` | 10, 5, 6 → **0** | 12, 5, 7 → **0** |
| `Collections`, `CollectionsHelpers`, `BlockEncryptor` | 1, 0, 0 → **0** | 18, 0, 2 → **0** |
| `GoldreichLevinDomain`, `InnerProduct` | 2, 3 → **0** | (= A) → **0** |
| `Primality`, `Chebyshev`, `Entropy`, `LeftoverHash` | 1, 1, 5, 1 → **0** | 2, (= A), (= A), (= A) → **0** |
| `RSA`, `Rabin`, `DDH` | 0 → 0 | 3, 3, 1 → **0** |
| `Concrete`, `DyadicUniform`, `BooleanVector`, `CollisionResistant`, `FromDiscreteLog` ×3, `Relational`, SeedMajority ×2 | 0 → 0 | 0 → 0 |
| `SamplingFinDist` | 2 → **1** | (= A) 2 → **1** |
| `SIS/CollisionOutput` | 1 → 1 | 1 → 1 |
| `Candidates/Factoring` | 0 → 0 | 22 → 24 |
| `HardCorePermutation/GoldreichLevin` | 0 → 0 | 8 → 8 |

Every remaining failure is mapped by enclosing declaration (`tools/errdecl.py`; `seal/d2/errdecl/`,
`seal/base/errdecl/`). None is outside an item the report lists:
- **`SamplingFinDist`:** `statClose_iff_epsClose_map`, the `EpsClose` residue of S2-SL-214 (§3, item 2; Q-D2-1).
- **`CollisionOutput`:** the `@[simps!]` attribute at l.53. It fails identically at the base. It is not an S2-A item
  (Q-D2-5).
- **`Factoring` B:**
  - **At the head:** the failures are only in the 9 declarations left in A30 (§5).
  - **At the base:** they were in those 9, plus `fmult_inLen`, `fmult_outLen` and `eval_fmultBlocks`, which A30 fixed.
  - **Why 22 → 24:** with the length readers fixed, elaboration gets further inside the remaining declarations. No new
    declaration fails.
- **`GoldreichLevin` B:** the 6 A37 declarations, with the same set at the base and the head (§5).

**Lints** (`lint/`):
- **`style_lint` on the 39 files** (D1's head vs D2's head):
  - **New findings:**
    - `OneWay.lean` 1,095 lines and `OneWayYao.lean` 1,005, both over 1,000 ("must split"). They were 995 and 976.
    - No **Proof sketch.** on four proofs that grew past 20 lines:
      - `Collections.toCollection_sampleClose` (23);
      - `EnsemblesLemmas.acceptProb_multicopyRed_congr` (24);
      - `HardCoreLemmas.owpPredMachine_predProb` (22);
      - `OneWayYao.statClose_sampleAll` (21).
  - **Size changes only:** `Collections` 1,124→1,170, `Factoring` 1,814→1,808, `RSA` 2,433→2,435 and
    `Rabin` 3,558→3,563 were already over the limit.
  - **Line shift only:** DyadicUniform's "`theorem in` has no docstring" finding (a parse artifact) moved line.
  - **Not fixed now:** a fix would have invalidated the replay. See Q-D2-3.
- **`campaign_style_lint --check8b`** over `TCSlib/Complexity` and `TCSlib/Cryptography`:
  - **FAIL:** 25/92, unchanged.
  - **WARN:** Complexity 389, unchanged. Cryptography 103→105, from the two new size WARNs (`OneWay`, `OneWayYao`).
  - **Shrinks:** the check-8 lists lose `input`, `LengthRegular`, `sampleAll` and `glBit`.
- **Line width:** every added line is at most 100 characters.

**decls2** (`decls2/`, `maintainer/tools/decls2.py`, which tracks statements of public declarations):

| vs D1's head | Declarations | Ruled item |
|---|---|---|
| ADDED (9) | `HardcoreBit.glBit_eq`, `FunFamily.lengthRegular_iff`, `ofString_inLen`, `prod_inLen_eval`, `prod_outLen_eval`, `OneWay.YaoMachine.yaoRaw_eq`, `sampleAll_eq`, `SelXor.input_eq`, `Collection.owfFamily_inLen_eval` | S2-RD-15, RD-09/10, S2A-N05, RD-11/12, RD-08, S2A-N06 (planned readers) |
| CHANGED (9) | `Ensemble.copies_X` | S2-BO-041 (Q8, Q-A9 a) |
| | `EnsembleLemmas.take_drop_ofFn_blocks`, `exists_copiesRed` | DL-35 #1/#3 (S2-BK-01/03) |
| | `FunFamily.ofFn_ofString_f`, `ofString_id_f`, `prod_f`, `PermFamily.toFunFamily_f` | S2-BO-006/007/073/080 (Q8, Q-A9 a; Q-A8 a keeps `@[simp]`) |
| | `FunFamily.glPad_f`, `glBit_append` | S2A-N08/N09 (Q-A3 a) |
| REMOVED | none | — |

- **Against the S2-A base** (`61a5f0fb`):
  - 38 ADDED, which are D1's 29 plus D2's 9, with `decide_singleton_eq_true` counted on the ADDED side of D1's move
    pair;
  - 13 CHANGED, which are D1's 4 `extTape` plus D2's 9;
  - 4 REMOVED, which are D1's 3 `host_*` and the `decide_singleton_eq_true` move.
- **Unmatched:** none. Every CHANGED and REMOVED entry matches a ruled item.
- **Private headers:** decls2 does not track private declarations. The three private header restatements are ruled:
  - `Collection.collInverter_success` and `fiber_le` (S2-BO-036/037, Q8);
  - `invProbAt_reduction_ge` (S2A-N10, Q-A3 a).
- **Deleted private declaration:** `fac_ofFn_halves` (S2-DL-26).
- **Kept private declaration:** `ofFn_chunk` (§3, item 1).

## 3. Deviations from the plan text

None of these changes a statement beyond the ruled ones, and none adds an unplanned declaration.

1. **S2-DL-24 (A19).** `Primality`'s `chunk` is not definitionally `FunFamily.blocks`. The plan's fallback therefore
   applies: the private `ofFn_chunk` is kept and re-proved from `FunFamily.ofFn_blocks`, through `chunk_apply` and
   `FunFamily.blocks_apply`.
2. **S2-SL-214 (A19), partly done.** The second direction of `statClose_iff_epsClose_map` now reads `EpsClose` through
   `epsClose_iff_statDist_le` and `abs_probTrue_sub_le_statDist`. The first direction still introduces `EpsClose`
   definitionally (l.66, `intro h D`). No published reader unfolds `EpsClose`: `rg "theorem (epsClose|EpsClose)"` finds
   only `epsClose_iff_statDist_le`, `EpsClose.symm` and `EpsClose.trans`. The residue is 1 error under both seals
   (Q-D2-1).
3. **Needs-check items: diagnosis and fix.**
   - **SL-280** (`exists_samplePrime_nuppt`). The failing read was the matcher of `polyTimeComputable_iterateFind`
     against the file's own `spFind_eq` matcher.
     - **Fix:** use `polyTimeComputable_iterateFind_elim` (A02's reader), with `spFind_eq` read at each search value.
   - **SL-155..157 (A21) and `Indist.copies` (A26).** The open goal was a `decide` whose instance still read
     `NUPPT.runAt`: simp transports the proposition but not the instance.
     - **Fix:** the verdict equation is proved as `Bool.eq_iff_iff`, reading `decide _ = true` first
       (`decide_eq_true_eq`) and the run after.
   - **SL-204/205 and SL-208..213 (A22).**
     - `statClose_sampleAll` goes through `sampleAll_eq` and `ρPEquiv`, round by round.
     - `exists_yaoReduction` identifies A's coins with the round coins by an explicit `Equiv.arrowCongr (finCongr hA)`.
4. **Row placement inside one declaration.**
   - S2-SL-164..171 (A36 in the TSV) are inside `StrongOneWay.glPad`, `glPad_hardCore`, `glPad_f` and `glBit_append`.
     They were done in A35, with the statements they read (Q-A3).
5. **S2A-N10 (A29, Q-A3 a).** The restated private `invProbAt_reduction_ge` writes the reduction's family as a literal,
   `⟨.var, L, fun m x => g m (x ∘ Fin.cast (PolyExpr.eval_var m).symm)⟩`, with no helper definition.
   - **Consumer:** `fUniversal_hard` applies it to `g` read through `PolyExpr.eval_var`. The resulting family is
     definitionally `⟨var, L, g⟩`.
6. **S2-RD-09/S2A-N05 (A23).** `FunFamily.ofString_inLen` is placed before `ofString_inLen_eval`, which now uses it.
7. **S2-BO-080 (A24, Q-A8 a).** `PermFamily.toFunFamily_f` keeps `@[simp]`. It moved after the two equivalences its new
   statement names.
   - **Downstream simp probe:** `HardCorePermutation/GoldreichLevin`, the consumer, compiles unchanged unsealed and has
     0 coe-A errors at D2's head.
8. **S2-BO-055 (A34).** The change to `Collection.glPad` is in the proof field `sample_spec` only. The data fields are
   unchanged, which the `rfl` probe confirms.
9. **A30, partial.** Done:
   - `fmult_inLen`, `fmult_outLen` and `eval_fmultBlocks`;
   - the DL-38 deletion of `fac_ofFn_halves`, whose three uses read `FunFamily.ofFn_blocks`.

   The rest needs the `fmult`/`plantFactor` body casts and three restated headers, with consumers across a 1,800-line
   file. It did not fit in this batch. A draft is kept at `$SP/s2a-d2/Factoring.draft.lean`, uncompiled under seal. See
   §5 and Q-D2-2.
10. **A37, not done.** `GoldreichLevin` is unchanged.
    - **Unsealed and coe-A:** it compiles against the new `Functions`/`OneWay`, and coe-A gives 0.
    - **Coe-B:** it keeps the planned items' failures (S2-BO-064..069, at l.602–726).
11. **A38.** It also carries the Q-D1-1 (a) fix: both `## References` labels now read "final paragraph of the proof".
12. **Pre-existing failure, not an item.** `SIS/CollisionOutput.lean:53` fails under both seals: `@[simps!]` on
    `rawCollisionInputs` needs the sealed body of `splitCoins` (Q-D2-5).

## 4. Helpers and duplication

- **New public declarations:** only the planned readers (decls2 ADDED). There are no new helper lemmas or definitions.
- **Searches before each reader** (`rg` over `TCSlib`; none found an existing reader of the same content):
  - `glBit (x, r) = ip`;
  - `theorem input_(eq|def)`;
  - `lengthRegular_(iff|def)`;
  - `theorem (yaoRaw|sampleAll)_`;
  - `ofString_inLen`;
  - `prod_(in|out)Len_eval`;
  - `owfFamily_inLen`.
  
  `Collection.glBit_eq` exists, but it is a different statement in another namespace.
- **Casts:** they go through `List.ofFn_congr` and `ofFn_arrowCongr_finCongr` (`Adversary.lean:234`).
  `rg "theorem \w*ofFn\w*(cast|arrowCongr|finCongr)"` finds nothing more general.
- **Local `have`s** are inline readings through published lemmas: `hf`, `hI`, `hg`, `hpe`, `hcast`, `hW`, `hinj`,
  `hx`/`hy`, `hA`, `hS'`, `hMg'`, `hmF`.
- **`hbridge`**, disclosed:
  - **What it is:** a local equation, `𝓕.glPad.invProbAt M n = invProbOpt (appendEquiv ∘ HardcoreBit.glPad … ∘
    appendEquiv⁻¹) (M.inverter …)`. At D1 it held by unfolding the definition.
  - **Where:** it appears twice, about 25 lines each, in `StrongOneWay.glPad` and `StrongOneWay.glPad_hardCore`
    (`HardCore/Functions.lean:386` and `:456`).
  - **Not a public re-proof:** `rg "theorem \w*invProb\w*(equiv|congr|reindex|comp)"` and the `HardCoreLemmas`
    statements (`invProbOpt_glPad_le` starts from the `invProbOpt` side) show no published lemma of this content.
  - **Status:** it is an in-file duplicate. Factoring it out would be a new private declaration, which the plan does not
    have (Q-D2-4).
- **Re-proofs:** no inline derivation re-proves a public TCSlib or Mathlib fact.
- **Ledger:** DL-62 is recorded (Q-D1-3 a). `dbl_append` was not moved.

## 5. Items left undone

- **A30 rest** (9 rows):
  - S2-BO-111 `exists_plantFactorer`;
  - S2-BO-112 `fac_prodInverter_eq_yaoB` (header);
  - S2-BO-113 `fac_strong_key`;
  - S2-BO-114 `fac_weak_key`;
  - S2-BO-115 `fmult` (body);
  - S2-BO-116 `fmult_easy`;
  - S2-BO-117 `fmult_f` (header);
  - S2-BO-119 `fmult_inv_factor` (header);
  - S2-BO-121 `plantFactor` (body).
- **A37** (7 rows):
  - S2-BO-064 `glHalfOddInv_runAt`;
  - S2-BO-065 `glHalfOddPred_runAt`;
  - S2-BO-066 `glHalf_invProbAt_even`;
  - S2-BO-067 `glHalf_predProb_even`;
  - S2-BO-068 `oddCoins` (body);
  - S2-BO-069 `ofFn_oddCoins` (header);
  - S2A-N07 `oddParam_eval` (private reader).
- **Partial:** S2-SL-214 (§3, item 2).
- **Records:** S2A-N03 is the records edit, and it is in `4f3ac57f0`.

## 6. Questions for Seyoon (recommended option first)

- **Q-D2-1. The `EpsClose` residue in `SamplingFinDist`** (l.66).
  - **(a) Recommended:** in D3, add the reader `epsClose_iff : EpsClose ε p q ↔ ∀ D, |p.probTrue D - q.probTrue D| ≤ ε
    := Iff.rfl` to `InformationTheory/Extractors.lean` (a new declaration, so it needs this ruling). Then finish
    S2-SL-214 with it.
  - (b) Accept the residue: 1 coe-A/B error remains in `SamplingFinDist`.
- **Q-D2-2. The steps left (A30 rest, A37; 16 rows).**
  - **(a) Recommended:** a batch D3 on this branch, from `a1545eae`. It finishes A30 from the kept draft and does A37,
    with an incremental replay from the D2 tree.
  - (b) Hand them to another job, or to Stage 3.
- **Q-D2-3. The lint regressions** (two files over 1,000 lines, four missing proof sketches).
  - **(a) Recommended:** in D3, add the four proof sketches and bring `OneWayYao` under 1,000 lines by trimming its
    docstrings. Both are docstring-only. Queue the `OneWay` split (1,095 lines) for Stage 3 with the other size splits.
  - (b) Split `OneWay` in D3 as well. This moves declarations, which no Stage 2 ruling covers.
  - (c) Accept them for Stage 3.
- **Q-D2-4. The duplicated local `hbridge`** (§4).
  - **(a) Recommended:** in D3, factor it into one private lemma beside `glPad_inEquiv_ofFn`, with a docstring and
    source tag. This is an unplanned private declaration.
  - (b) Keep the two inline copies.
- **Q-D2-5. `CollisionOutput`'s `@[simps!]` failure under seal** (pre-existing, not an S2-A item).
  - **(a) Recommended:** record it for S2-D or Stage 3. It needs explicit `@[simp]` field lemmas in place of `simps!`,
    or a `splitCoins` reader.
  - (b) Fix it in D3.
- **Q-D2-6. Trees.**
  - **(a) Recommended:** keep `$SP/olean-replay-s2a-d2` as D3's starting tree, to adopt or discard with S2-A. Delete
    D1's tree `$SP/olean-replay-s2a-d1` now, since D2's tree holds every inode it needs. The coordinator decides on
    `$SP/olean-snapshot-10`, which `snapshots.md` says to delete after D2.
  - (b) Keep both trees until S2-A merges.

**Not yet clear to merge — A30 (rest) and A37 remain (Q-D2-2); seal residues Q-D2-1 and Q-D2-5 and lint Q-D2-3 need rulings.**
