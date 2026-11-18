# EF-H12 `ef-h12-levin-3col` · final r1 · phase 2: merged-tree replay on olean snapshot #11

**Verdict: PASS, with one new minor finding (EFH12-F08).** The replay ran on a scratch stack of the 19
delivered patches on `bff0567b`, whose tree equals phase 1's `merge-tree` prediction. `bff0567b` is
Lean-equal to the records tip `a085848f`.

- **Build.** 16/16 modules rc 0, exactly the predicted 16. There were 0 `error:`/`error(`, 0 `sorry`
  and 0 warnings. The 16 include the root `TCSlib` and `audits/pass-shelat/Checks`, so
  **EFH12-F04 is closed.**
- **Axioms.** The census covers 483 stored constants of the 12 new modules and the facade, and all
  are within `propext`/`Classical.choice`/`Quot.sound`. The 245 decls2 constants are all present,
  and their axiom sets equal the worker's `stmtdump.txt` one for one. The headline and both
  corollaries are `[propext, Classical.choice, Quot.sound]`. The `sorry` control is flagged.
- **Seals** (closes the evidence gaps of EFH12-F03):
  - **Strict:** the worker's own whole-file seals, re-run here, give 11/11 rc 0 with 0 errors.
  - **Canonical coe-A:** 10 of 11 owners give 0 errors. **`Verifier` fails exactly once, in
    `polyTimeComputable_stripCert`.** That proof identifies `stripCert` with the catalog function of
    `Turing.FinTM.computesFunInTime_stripLast` by defeq through that theorem's compiler-generated
    matcher `Turing.FinTM.stripLastTM_computes.match_1`. This is the **new minor EFH12-F08**, of the
    dl-c `dlc_ssLoop_poly` class.
  - **Seal B** (`PolyExpr.eval` sealed too) gives the same single failure, and nothing else.
- **`Bridge.lean`, minimal unseal.** All 27 declarations compile when each is unsealed for **only**
  the definition it is named for, so the worker's 9 over-broad unseals are unnecessary. With **no**
  unseal, 20 of them fail. The other 7 are the `simp [EdgeRelation]` case lemmas, and they pass with
  `EdgeRelation` sealed: they read the definition through its equation lemmas, which the seal
  cannot block. The explicit-unfold scan flags exactly these 7 (see EF-H12-R1).
- **Controls:** 50 paired controls, one per new public definition. Each NEG fails exactly once, no
  POS fails, and the open file has 0 errors: **ALL_OK**.
- **Bridge demonstrations (R1).**
  - **Necessity:** with the 20 bridged definitions sealed and every reader use proved in place, each
    of the 46 reader uses in the 4 consumers fails.
  - **Owner form:** the 27 readers compile verbatim appended to their 5 owner files, with no extra
    import.
- **Landing-edit probes.**
  - **F02:** `unaryPow_poly` from `unaryPolyOf_poly (.pow .var n) hf` compiles, and its 10-module
    downstream rebuilds rc 0.
  - **F05a:** `ProbeH12.lean` passes at the check head.
- **Lint.** 92 FAIL / 103 WARN, with line sets unchanged; `style_lint` gives 0 findings.
- **Snapshot #11** rehashes 0/0/0 before, after the build and at the end.

Run on 2026-11-18, 12:23–13:36 UTC, as the review's *Phase 2 plan* describes and the coordinator
dispatched. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

- **Evidence:** `ef-h12-final-r1-evidence.zip`, beside this file. It holds `PROVENANCE.txt` and an
  inner `SHA256SUMS` that does not list itself. The zip's own SHA-256 is in `evidence-SHA256SUMS`.
- **Lean processes.** This job ran **one Lean process at a time**: 86 starts in all, with
  `mathlibextra` and the 16 build modules among them.
  - Every start went through `runq.sh`, which checks `pgrep -fc "bin/lean "` ≤ 2 and at least
    2,000 MB free before each start, and logs it in `logs/slot.log`. The one exception is
    `mathlibextra`, which had the same check done inline.
  - The host never had more than 2 Lean processes at once: this job's and S2-A D2's. No start had
    to wait.
- **Not done:** no `lake build`, no cache get, no branch, no push, no PR, and nothing committed.
- **Not touched:**
  - the snapshot (read and hard-linked only), `$SP/olean-snapshot-10`, `$SP/olean-replay-efh1`,
    `$SP/efh1/` and the S2-A trees and worktrees;
  - `/home/user/tcslib`, apart from this folder's outputs. The scratch worktree registration and
    the scratch commit objects are in its `.git`, but no ref was made or moved.

  Only this job's own PIDs were waited on, and none was killed.
- **Disk.** 3,459 MB was free at the start. The lowest reading at a Lean start was **3,076 MB**,
  and 3,077 MB was free at the end. No process slips.

## P2-0 Inputs

| Input | Result |
|---|---|
| **Records tip** | `a085848f35cec75cf8c65c2c78cf987f32ca2ef2`, the checked-out `cryptography/pass-shelat-ch2-4`. `git diff --name-only bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d HEAD -- TCSlib TCSlib.lean audits lakefile.lean lake-manifest.json lean-toolchain` is **empty**, so the tip is Lean-equal to snapshot #11's T. |
| **Delivery** | Fetched by name: `origin/exchange/pass-shelat-ch5-8` = `b11b9408b830b855b220ee1c3c80429abea6830c`. The delivery commit `36d9ac03` is an ancestor, and `inbox/fills/ef-h12-levin-3col/` is unchanged between the two (`git diff` empty). It was extracted with `git archive` from `36d9ac03`, and both manifests pass `sha256sum -c`. |
| **Snapshot #11** | Map `olean-snapshot.map-bff0567b.tsv` = `e7bb03b4…867d0` and files `olean-snapshot.files-bff0567b.txt` = `463c8869…0b13`, both re-hashed. `snapmap.py verify` before the copy: **0/0/0**, 1487 files, RESULT OK. |
| **Recipe tools** | `olean-advance-a6d01b1b/tools-used/` was extracted fresh from `olean-rebase-evidence.zip` (`b662b7da…`). It is byte-identical to EF-H1's copy (`diff -rq` empty), and the tools were used unmodified. |
| **Scan tools** | The gate-04 tools from the records' `gates/04-s2b/evidence-r5/tools/`, unmodified. They are byte-identical to the worker's `gate04-seal-tools` copies, except `mods.txt`, the input, which lists the 12 new modules. |

**New tools** (in the zip's `tools/`):
- `stack.sh` (P2-1);
- `runq.sh`, the per-start slot and disk check, adapted from EF-H1's;
- `probes.sh` and `seals.sh` (probe and seal batches through `runner_full.py`);
- `le.sh` (the F02 rebuild);
- `mkctl.py` (controls);
- `mkbridgemin.py` (minimal unseal);
- `mkowner.py` (owner form);
- `mknec.py` (necessity);
- `recount.py` and `sealparts.py` (recounts).

## P2-1 Scratch stack and check head (scratch only, never pushed)

- **Worktree.** A detached sparse worktree `$SP/efh12/p2/wt`, with sparse set
  `TCSlib/Cryptography/ZeroKnowledge/`, its facade and `lean-toolchain`.
- **Reproduction first.** `git am` of the 19 patches at REC `cf6a2266`, unsigned, with each commit's
  committer data from `COMMITS.tsv`. **All 19 hashes reproduce**, ending at
  `c8d5b3c7f8733f3ea87fc701fbc83abc53bdb338`.
- **Check head.** The same 19 patches, applied by `git am` on `bff0567b` (unsigned, with a fixed
  committer date of `12:00Z`), give **`63d619e8440969a4afc06d5274b55c418cf309f7`**, with tree
  **`efdd41d867a0d057d7fce00b915aedcc743138f3`**.
  - This is the expected tree, and it equals `git merge-tree --write-tree c8d5b3c7 bff0567b`.
  - The commits carry 0 `gpgsig`.
- **Diff against `bff0567b`:** exactly the 14 delivery paths, +4,000/−0.
- **Sources.** All 14 head files equal the delivered `src/` byte for byte.

## P2-2 Replay (snapshots.md job recipe)

- **Copy and overlay.**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-efh12`: 1487 files, all hard links.
  - `mloverlay.sh` made 3346 Mathlib symlinks.
  - `mathlibextra.sh` built `NthRootLemmas` with rc 0; its olean is **`c0a9cff0…`**.
- **Tree.** `git archive` of the check head (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the lake
  files, `lean-toolchain`; 1621 files), with `.lake/packages` symlinked. The 14 delivery sources in
  the export equal `src/` (`logs/export-vs-src.log`).
- **Plan.**
  - `stateplan init` at `bff0567b`: 1456 modules.
  - `downorder.py`: **changed 14, down 16**. The 14 are the 13 new modules and the `ZeroKnowledge`
    facade; the down set adds the root `TCSlib` and `audits/pass-shelat/Checks`.
  - `fullorder.py`: 1469, with roots `TCSlib` and both `Checks`.
  - `stateplan plan`: **16 to build, 1453 reused**, exactly the review's prediction.
  - `audits/garg-ch1-3/Checks` is reused, as predicted.
- **Build.** 12:25:30–12:28:39.
  - **16/16 rc 0.** `error:` 0, `error(` 0, the substring "error" 0, `sorry` 0, warnings 0.
    `permod.py` finds no log/record mismatch.
  - The queue order matched the predicted import order: Relations, Bridge, Verifier,
    CircuitWitness, Gadget, UnaryArith, ColoringGraph, ColoringParse, ColoringWitness, Soundness,
    Padding, Hardness, the two facades, `TCSlib`, then `Checks`.
  - **Sources bound** (`logs/source-binding.log`). Every record's source SHA-256 equals
    `git show 63d619e8:<path>`. The 14 delivery modules' hashes also appear in the worker's
    `build/summary.txt`.
  - **Times.** The new modules took 1.6–18.3 s each; the slowest were `ColoringWitness` (18.3 s)
    and `ColoringGraph` (12.1 s). The root took 3.3 s and `Checks` 121.7 s. Peak maxrss was
    4.58 GB (root).
  - **This closes EFH12-F04.** The root elaborates with the delivery on snapshot #11's PFR oleans,
    and so does `audits/pass-shelat/Checks`, which imports the changed `ZeroKnowledge` facade.
- **Accept.**
  - `stateplan update`: 16 modules, none left out.
  - `check` over the full order: **1469/1469, RESULT OK**. It still gives RESULT OK at the end of
    the job, after every probe (`logs/stateplan-check-end.log`).
  - **Link count 1** for all 16 rebuilt oleans. Exactly 16 non-Mathlib oleans in the tree have link
    count 1 (`logs/rebuilt-oleans.sha256`), and their hashes are unchanged at the end.
  - `snapmap.py verify` after the build: **0/0/0**.

## P2-3 Axioms

`Axioms` (the recipe's `AxiomProbe.r2.lean` form, with the owner list replaced by the 12 modules and
the `LevinHardness` facade, the 3 headline names by name, and a `sorry` control): rc 0, 43 s.

- **Stored constants: 483.** 259 named, 224 auxiliary.

  | Axiom set | Constants |
  |---|---|
  | `[Classical.choice, Quot.sound, propext]` | 190 |
  | `[Quot.sound, propext]` | 134 |
  | `[propext]` | 96 |
  | `[]` | 63 |

  **0 non-standard.**
- **The 245 decls2 constants are all present.** Their sets are 116 `[Classical.choice, Quot.sound,
  propext]`, 38 `[Quot.sound, propext]`, 44 `[propext]` and 47 `[]`. This is phase 1's recount, and
  each of the 245 equals its row in the worker's `axioms/stmtdump.txt` (`logs/axioms-vs-worker.txt`).
- **The 238 other rows** are auxiliaries: `_proof_N`, `match_N`, `eq_N`, `_simp_N`, and similar.
- **Headline and corollaries.** `levinNPHard_L3COL`,
  `zk_proof_of_witnessRelation_of_owp_unconditional` and `zk_proof_of_mem_NP_of_owp_unconditional`
  are each `[propext, Classical.choice, Quot.sound]`. This holds both in the census and in
  `#print axioms`.
- **Control.** `efh12SorryControl` reports `[sorryAx]`, and its `sorry` warning is the probe's only
  warning.

## P2-4 Seals

**Collector.** `mkcollect.py` with the 12 new modules gives `Collect`: rc 0, 0 errors, and 7,059 CAT
rows. The stored-constant counts per module are Relations 4, Bridge 42, Gadget 20, Padding 27,
UnaryArith 7, Verifier 30, CircuitWitness 45, ColoringGraph 128, ColoringWitness 42,
ColoringParse 91, Soundness 36 and Hardness 11.

**Canonical coe-A** (`mkseals_coe.py`, A variant, unmodified, `SEAL_CHUNK=1000` as in the EF-D1 and
EF-H1 precedent; `sealsum.py`; `sealparts.py`):

| Owner | Requests | Terms | Excluded terms | Parts | Result |
|---|---|---|---|---|---|
| `Relations` | 191 | 5 | 0 | 191 | **rc 0, 0 errors** (15 s) |
| `Verifier` | 2,150 | 18 | 1 (`PolyExpr.eval`, notation) | 1000+1000+150 | **rc 1, 1 error**: `polyTimeComputable_stripCert` (src line 133), F08 (130 s) |
| `CircuitWitness` | 4,805 | 34 | 4 (abbrevs) | 4×1000+805 | **rc 0, 0 errors** (302 s) |
| `Gadget` | 1,052 | 1 | 1 (abbrev `Graph`) | 1000+52 | **rc 0, 0 errors** (119 s) |
| `UnaryArith` | 1,059 | 5 | 0 | 1000+59 | **rc 0, 0 errors** (96 s) |
| `ColoringGraph` | 1,942 | 22 | 7 (abbrevs) | 1000+942 | **rc 0, 0 errors** (106 s) |
| `ColoringParse` | 2,550 | 26 | 1 (`PolyExpr.eval`) | 1000+1000+550 | **rc 0, 0 errors** (175 s) |
| `ColoringWitness` | 1,854 | 13 | 0 | 1000+854 | **rc 0, 0 errors** (139 s) |
| `Soundness` | 2,550 | 22 | 5 (abbrevs) | 1000+1000+550 | **rc 0, 0 errors** (177 s) |
| `Padding` | 1,847 | 10 | 1 (abbrev `Graph`) | 1000+847 | **rc 0, 0 errors** (111 s) |
| `Hardness` | 4,863 | 49 | 2 (`PolyExpr.eval`, `Graph`) | 4×1000+863 | **rc 0, 0 errors** (354 s) |

- Every part has install and end records, and every end record gives `verified = requested`.
- **Why the request counts are higher than the worker's** (5 to 48 candidates per file). As in
  EF-D1 and EF-H1, the recipe collector requests every ordinary TCSlib definition of the owner's
  transitive closure, **matchers included**. This is the stricter seal, and it is the reason it
  finds F08.

**EFH12-F08 (new, minor): a definitional read of a foreign matcher in `polyTimeComputable_stripCert`**
(`Verifier.lean:131-134`).
- **What happens.** The proof is `exact (polyTimeComputable_iff _).2 ⟨M, c, 2, hM⟩`. The type of
  `hM`, from the catalog theorem `Turing.FinTM.computesFunInTime_stripLast`
  (`TuringMachine/Build/Primitives.lean:3259`), states its function as an anonymous `match`. Lean
  compiles that `match` to the foreign matcher `Turing.FinTM.stripLastTM_computes.match_1`. The
  proof checks it against `stripCert` by unfolding `stripCert` and identifying the two matchers by
  defeq.
- **Attribution** (`StripProbe`, sections S0/S1):
  - unsealed, the delivered proof passes;
  - with **only** `Turing.FinTM.stripLastTM_computes.match_1` locally irreducible, it fails with the
    same "Application type mismatch" as under the seal.
- **Precedent.** This is the class of dl-c's `dlc_ssLoop_poly` (`delivery-review-dl-c.md` item 3): a
  compiler-generated matcher in a cited theorem's statement. It is minor, not a Rule-10 violation in
  substance, but avoidable.
- **Not seen in phase 1.** The worker's strict candidate lists do not include matchers, and phase 1
  recounted those lists. Phase 1's "0 foreign unfolds outside Bridge.lean" holds for the text scan
  (below), but not for this definitional read.
- **Candidate landing edit (LE-h12-strip).** Transport along `stripCert_eq` and split both matches:
  `refine (polyTimeComputable_iff _).2 ⟨M, c, 2, ?_⟩; convert hM using 2; rw [stripCert_eq]; split
  <;> split <;> simp_all`. In `StripProbe` (attempt 2), this form (F1), and its `repeat' split`
  variant (F3), compile with the matcher and `stripCert` both sealed. The `rcases`/`simp` form (F2)
  fails. Attempt 1 failed only because `convert … using 2` had already applied `funext`.
- **Caveat on the fix.** Under the cleanup "N4 boundary", a pass that rests on constructor-discriminant
  reduction of a sealed foreign matcher is not acceptance by itself. Before the fix lands, its
  proof term should be checked to go through the matcher's splitter and equation lemmas, and the
  canonical seal of `Verifier` re-run.

**Seal B** (`SEAL_EVAL=1`, which also seals `PolyExpr.eval`): requests are one higher per owner
where `PolyExpr.eval` is in the closure (Verifier 2,151, ColoringParse 2,551, Hardness 4,864, and so
on).
- 10/11 owners give rc 0 with 0 errors, and every part gives `verified = requested`.
- `Verifier` again fails only at `polyTimeComputable_stripCert`, the same line and the same error.
- **So no new proof reads `PolyExpr.eval` by defeq.**

**Strict** (the worker's 11 `seals/plain/*_plain.lean`, re-run unchanged):
- Each was checked first to be the head source plus exactly one seal line; Gadget's line is the
  comment `-- (no candidates)`.
- **11/11 rc 0, 0 errors.** This reproduces the worker's `results_plain.txt`.

**`Bridge.lean`, minimal unseal** (`BridgeMin`, from the worker's strict sealed copy by
`mkbridgemin.py`):
- **Setup.** The script asserts that the copy, minus its seal and unseal wrappers, equals the head
  source byte for byte. The seal line is the worker's 20 names, equal to its candidate list. Each
  `section … attribute [local semireducible] … end` is then rewritten to name only the declaration's
  own definition.
- **Result: rc 0, 0 errors.** Every one of the 27 compiles unsealed for **only** the definition it is
  named for.
- **No-unseal control** (`BridgeNone`, the same file without any unseal line): 43 errors.

| Declaration(s) | Minimal unseal | Fails with no unseal | Worker's unseal |
|---|---|---|---|
| `levinNPHard_iff` | `LevinNPHard` | yes (1) | same |
| `toCNF_eq` | `DAGCircuit.toCNF` | yes (1) | **+`tseitinGates`, not needed** |
| `widthAtMost_iff`, `numVars_eq`, `serializeLit_eq`, `fallback_eq` | own definition | yes (1 each) | same |
| `serializeClause_eq` | `serializeClause` | yes (1) | **+`serializeLit`, not needed** |
| `serialize_eq` | `serialize` | yes (1) | **+`serializeClause`, not needed** |
| `decode_eq` | `decode` | yes (1) | **+`fallback`, `parse`, not needed** |
| `syntaxStep_eq` | `syntaxStep` | yes (12) | same |
| `syntaxOK_eq` | `syntaxOK` | yes (1) | **+`syntaxStep`, not needed** |
| `satisfiesLiteral_pos`, `_neg`, `is3Colorable_iff` | own definition | yes (1 each) | same |
| `satisfiesClause_eq` | `SatisfiesClause` | yes (1) | **+`SatisfiesLiteral`, not needed** |
| `satisfiesSat3_eq` | `SatisfiesSat3` | yes (1) | **+`SatisfiesClause`, not needed** |
| `isSatisfiable_iff` | `IsSatisfiable` | yes (1) | **+`SatisfiesSat3`, not needed** |
| `reductionGraph_adj` | `ReductionGraph` | yes (1) | **+`EdgeRelation`, not needed** |
| `edgeRelation_literal_gadget` (`cases z <;> rfl`) | `EdgeRelation` | yes (2) | same |
| `edgeRelation_gadget_literal` (`cases`/`fin_cases` + `rfl`) | `EdgeRelation` | yes (12) | same |
| the 7 `simp [EdgeRelation]` lemmas (`palette_palette`, `palette_literal`, `literal_palette`, `literal_literal`, `gadget_gadget`, `gadget_palette`, `palette_gadget`) | **none** | **no: they pass with `EdgeRelation` sealed** | `EdgeRelation` (not needed) |

- **The minimal-unseal list is therefore:** 20 declarations, each needing exactly its named
  definition, and 7 needing nothing.
- **The 7 read `EdgeRelation` through its generated equation lemmas.** They pass it to `simp`, which
  a `local irreducible` seal cannot block. The gate-04 scan below flags exactly these 7 lines.
- **This settles the F03 sub-point.** "Unsealed for exactly its own target" is now shown, and the 9
  over-broad unseals were not needed.
- **It adds a fact for R1:** 7 of the 27 readers are not definitional reads at all, but
  equation-lemma reads of a foreign definition (COMMON §4.3).

**Paired controls** (`Ctl_sealed`/`Ctl_open`, generated by `mkctl.py` from `probe-src/ctl-pairs.tsv`;
recount in `rule10/controls-recount.txt`):
- **Coverage.** 50 pairs, one per new public definition (decls2's 50 `def` rows).
- **Form.** Each pair is a section that seals only that definition, then:
  - NEG reads the body: the reader's statement by `intros; first | exact rfl | exact Iff.rfl`;
  - POS uses the reader.
- **Three NEGs are explicit body reads.** The `_eq`/`_iff` readers of `goodS` and `memS` are
  specifications, not restatements, and `tabInst_eq` is a theorem. So the NEGs for these three are
  explicit body reads (`goodS`, `memS`) or use `tabInst_def`. The first attempt (`rule10/b1`) found
  the three NEGs that fail even unsealed; it is kept.
- **Result: ALL_OK.**
  - Sealed: exactly 50 errors, one at each NEG line, and none at a POS line or anywhere else.
  - Open: 0 errors.
- The worker's 9 pairs are a subset of the definitions covered.

**Explicit-unfold scan** (the gate-04 `scan.py` on the 12 files, with the constant table and
equation-lemma lists from the gate-04 collector `G04Collect`, rc 0; `rule10/unfold-scan.txt`):
- **7 hits:** the 7 `simp [EdgeRelation]` lines of `Bridge.lean` (166, 171, 176, 183, 193, 215, 222).
- 0 `show`/`change` at seal failures, and 0 proof-term references to a foreign equation lemma.
- **0 hits outside `Bridge.lean`.**
- **Comparison with the worker.** The worker's adjudicated scan listed 6 more hits
  (CircuitWitness:223 ×4, ColoringGraph:300, ColoringParse:203), which it then cleared as lemma
  arguments. The records' `scan.py` does not report them at all. This agrees with phase 1.
- **Not run:** the scan's optional second collector pass, which only adds `src:`-tier candidate
  statements.

## P2-5 Bridge demonstrations (for R1)

1. **Necessity** (`mknec.py`; `rule10/necessity-recount.txt`).
   - **Setup.** Two copies of each consumer:
     - *sealed*: the 20 bridged definitions locally irreducible, and every code use `Bridge.X`
       replaced by `(by intros; first | exact rfl | exact Iff.rfl : type_of% @Bridge.X)`, i.e. the
       reader's statement proved in place by reading the body, so the reader's proof is not used;
     - *open*: the same replacement, unsealed.

   | Consumer | Reader uses | Sealed: errors | Open: errors |
   |---|---|---|---|
   | `CircuitWitness` | 1 (`toCNF_eq`) | 1, at the use | 0 |
   | `ColoringParse` | 26 on 23 lines | 27: one at every use line, plus 1 cascade (line 616, the enclosing `by`) | 8: the 7 `syntaxStep_eq` lines + 1 cascade |
   | `Soundness` | 16 | 16, one per use | 9: the 9 `edgeRelation_*` uses |
   | `Hardness` | 3 (`widthAtMost_iff` ×2, `levinNPHard_iff`) | 3, one per use | 0 |

   - **Every reader use fails** once the bridge's proofs are taken away and the definitions are
     sealed.
   - **The open copies separate two groups.** The 17 non-case readers are plain definitional
     restatements: their in-place reads pass unsealed. The 10 case lemmas (`syntaxStep_eq` and the
     9 `edgeRelation_*`) are not one-step `rfl` statements.
2. **Owner form** (`mkowner.py`).
   - **Setup.** Each owner file at `bff0567b`, byte for byte, with one appended block: `namespace
     TCSlib.Cryptography.LevinHardness.Bridge`, one owner-specific `open` line, and that owner's
     readers copied verbatim.

   | Owner | Readers | Result |
   |---|---|---|
   | `Formulas/CNF.lean` | `widthAtMost_iff`, `numVars_eq` | rc 0, 0 errors |
   | `Formulas/CNFEncoding.lean` | the 7 serialization and syntax readers | rc 0, 0 errors; 1 warning at line 646, in the owner's own text (`simpa` linter) |
   | `CircuitComplexity/DAGCircuitSat.lean` | `toCNF_eq` | rc 0, 0 errors |
   | `NPReductions/ThreeSATToColoring.lean` | the 16 course readers | rc 0, 0 errors |
   | `ZeroKnowledge/NP.lean` | `levinNPHard_iff` | rc 0, 0 errors |

   - All 27 readers compile in their owners **with no added import**, so an owner PR for them is a
     pure append. The probe sources in `probe-src/Owner_*.lean` give the text. Nothing was
     committed.

## P2-6 Landing-edit probes

- **F02 (LE-h12-pow).**
  - **The edit.** `unaryPow_poly`'s proof becomes the single line
    `simpa only [PolyExpr.eval_pow, PolyExpr.eval_var] using unaryPolyOf_poly (.pow .var n) hf`
    (`probe-src/UnaryArith_LE.lean`).
  - **Compiles.** As a probe: rc 0, 0 errors.
  - **Downstream rebuild.** As a scratch commit `7880f92458c3e894a4b8b09b49305c75197b6ff9` on the
    check head (tree `58ba3c4d…`, made with a temporary index, never pushed), its downstream was
    rebuilt on a separate hard-linked copy of the accepted tree (`le.sh`). The plan gave 10 to
    build and 1459 to reuse:
    - **10/10 rc 0**, with 0/0 errors, 0 `sorry` and 0 warnings;
    - `stateplan check` gives 1469, RESULT OK, and all 10 oleans have link count 1.

    The copy was then deleted. Its records are in `le/`, and the olean hashes are in
    `logs/le-rebuilt-oleans.sha256`.
- **F05a.** The delivered `evidence/probes/ProbeH12.lean`, unchanged, at the check head: **rc 0, 0
  errors**. Its kernel-`decide` checks on the `K = 1` gadget graph and the padding length pass
  against the final `Gadget.lean` and `ColoringWitness.lean`.

## P2-7 Lint

- `campaign_style_lint.py TCSlib/Cryptography --check8b`, on exports:
  - `bff0567b`: **92 FAIL / 103 WARN over 540 files**;
  - check head: **92 / 103 over 553**.
- **The FAIL/WARN line sets are identical** (diff empty), and equal phase 1's head output.
- `style_lint.py` on the 14 changed files: **0 findings**.

## P2-8 State after the run

- **Kept, for the gate:**
  - `$SP/olean-replay-efh12`: the accepted check-head tree, with 1487 hard links, the 16 rebuilt
    oleans, the `NthRootLemmas` olean and 3346 Mathlib symlinks. `stateplan check` gives RESULT OK
    at the end.
  - The scratch worktree `$SP/efh12/p2/wt`, detached at the check head `63d619e8`. It holds the
    probe directory `EFH12Probe/` with the seal copies.
  - The scratch commits `63d619e8` and `7880f924`. They are on no ref and were never pushed.
- **Deleted:**
  - the F02 tree `$SP/olean-replay-efh12-le`;
  - the evidence staging copy.
- **Also deleted:** the F02 and lint-baseline exports (`tree-le`, `lint/base`). The check-head export `$SP/efh12/p2/tree` is kept.
- **Snapshot #11:** `snapmap.py verify` gives **0/0/0** at the end (13:35Z).
- **Not in the zip:** the raw sealed-source copies. They are about 1–6 MB each and can be
  regenerated by `mkseals_coe.py` from the collector log in the zip. Their SHA-256 are in
  `rule10/seal/omitted-seal-sources-SHA256SUMS`.
- **In the zip:** the raw Lean logs of every seal run (`rule10/seal/runs-{A,B}/mods/`).

## What this changes in `review.md`

| Item | Phase 1 | After phase 2 |
|---|---|---|
| EFH12-F03 (seal evidence partial) | minor, open | **closed**: coe-A and seal B run with raw logs; per-declaration minimal unseal shown; 50 control pairs ALL_OK. The run found F08. |
| EFH12-F04 (C2 incomplete) | minor, open | **closed**: root `TCSlib` and `audits/pass-shelat/Checks` rc 0 |
| EFH12-F05 (stale evidence and text) | minor, open | **(a) closed** (`ProbeH12` passes at the head); **(b) closed** (independent 245-constant census); (c) still a landing edit (LE-h12-doc); (d) stays recorded |
| EFH12-F02 (UnaryArith duplication) | major, R3 | still open on R3; **LE-h12-pow verified**: it compiles, and its 10-module downstream is rc 0 |
| EFH12-F01 (bridge) | major, R1/R2 | still open on R1/R2. New facts: the minimal unseal; the 7 `simp` readers are equation-lemma reads the seal cannot see; necessity; owner form compiles |
| **EFH12-F08 (new)** | none | **minor, landing edit**: foreign-matcher defeq read in `polyTimeComputable_stripCert`; candidate LE-h12-strip compiles under the seal (caveat above) |
| C1, C5, C6, C8 and the worker's `ProbeH12` | recounted statically | **reproduced** by an independent replay |
