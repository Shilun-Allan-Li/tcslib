# Gate 42 · Yao's protocol in the OT-hybrid model (`sc-yao`, #341) · round 2

The auditor is Codex, under the standing ruling of 2026-11-11. Round 1 was **HOLD** (0 blockers, 1 major, 2 minors,
0 notes); its findings are `findings/gate42-sc-yao-findings.md` (SHA-256 `e1076c1e…`). It found no mathematical gap.
This round re-audits the fixes of G42-01 to G42-03, checks the integration evidence and its binding to the new head,
and checks that the round-1 confirmations still hold and that nothing new is undisclosed. The round-1 pack (`pack.md`)
still defines the scope; its questions stand for anything round 1 left unverified.

- **PR:** draft [PR #341](https://github.com/Shilun-Allan-Li/tcslib/pull/341), now at
  `355a0288d56290e8c984228cbc1824187029e456` (branch `land/pass-shelat-sc-yao`, pushed; tree
  `3cf1047be5c1dff4c3f4f6cffa4c926b6f0d1de7`). Round 1 audited `e9b03c437aca251846430ff23b40ee5ff3d3347a`.
- **Records pin:** `2da7e0f3cd65ec93ed71813b7828c3b66ba18942`, the records tip at staging. It descends from round 1's
  pin `f22e0f67`, the rulings `67423db6` (SY-F01 to SY-F03), `d6fe1ddd` (the DL-49 wording) and `bf08dbfa` (SY-F05,
  DL-52), the round-1 findings and resolutions (`9fa48035`) and the integration evidence (`ed0d2acc`). From `f22e0f67`
  to the pin, 25 records commits change no code path (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, lake files: 0).
  This pack's own files are filed by the maintainer after the pin.
- **Base, unchanged.** The merge base with the records branch is still `f9fda8fe8d11fc68c233df2979a86d356ddfe1ab`.
  **No rebase:** `e9b03c43` is an ancestor of the head. `pr.diff-r2.txt` is `git diff f9fda8fe..355a0288`, which
  equals the three-dot `git diff 2da7e0f3...355a0288` (GitHub's view) byte for byte. It has the same 70 paths and
  statuses as round 1 (68 added, 2 modified) and 15879 insertions, 67 deletions (`checks/series-r2.txt`).
- **New since round 1:** three commits on the first-parent chain. Each is by the maintainer (author and committer
  Claude) and carries one SSH signature. All three verify (ed25519) against the key that signs the records pin, and a
  one-byte tamper control fails:

  | Commit | Landing edit | Finding | Files | Size |
  |---|---|---|---|---|
  | `26f0b77b` | **LE-reuse-2**: `RunWithHost.acc_poly` from `StateLoop.MajLoop.acc_poly` | G42-01 (major) | 1 | +8/−3 |
  | `3e99eb80` | **LE-refs**: full `[AB09]` and `[BMR90]` entries | G42-02 (minor) | 2 | +5 |
  | `355a0288` | **LE-steps**: step comments in the six proofs | G42-03 (minor) | 6 | +56 |

  `pr-r2.diff.txt` is `git diff e9b03c43..355a0288`: 9 files, 69 insertions, 3 deletions.
- **Resolutions:** `resolutions-r1.md` (records `9fa48035`), and the decision-log rows of 2026-11-16 (bundle;
  `records/decision-log-sc-yao.md` in `verification-r2.zip`, lines 816–829 of the plan at the pin).
- **The earlier rulings stand:** SY-1 to SY-6; SY-F01 confirmed; SY-F02 ledger then promote (DL-51); SY-F03 ledger,
  promote later (DL-49 extended, with the `d6fe1ddd` wording); SY-F05's remaining pair ledger, re-point after #341
  merges (DL-52); the Rule 10 rulings (`PolyExpr.eval` notation, seal A canonical; the projection coercion, coe-A
  canonical); SY-2's 1,200-line cap for `Yao.lean`. Round 1 confirmed DL-49, DL-51 and DL-52 against the code. None
  of the three commits touches a declaration those rows name.

Lean paths below are under `TCSlib/Cryptography/SecureComputation/` unless they start with `TCSlib/`; helpers are
under `Yao/HybridProof/`. `M` and `M′` are the integration merges of § 6.

## Round-1 findings, resolutions and evidence

| Finding | Resolution | Evidence | What round 2 decides |
|---|---|---|---|
| **G42-01** major: `RunWithHost.acc_poly` (`RunWithHost.lean:88`) re-proves the public `Complexity.StateLoop.MajLoop.acc_poly` (`StringLoops.lean:144`), undisclosed | **LE-reuse-2** `26f0b77b`, proof-only: derived from `MajLoop.acc_poly` through the readers `acc_eq` and `MajLoop.acc_eq`; the docstring discloses the reuse | `le-r2.txt` § LE-reuse-2, `decls-r2.txt`, `closure-r2.txt`; on M′: `integration-r2.txt` (build, axioms with `#check`, four seals) | § 1: proof-only, reads only the published readers, statement and imports unchanged; closed? |
| **G42-02** minor: `ChunkScanner.lean` cites `[AB09, §6.2]` and `GarblingProgram.lean` cites `[BMR90]` without bibliography entries | **LE-refs** `3e99eb80`: the two full entries, module docstrings only | `le-r2.txt` § LE-refs, `sources-r2.txt` | § 2: comment-only; entries correct; closed? |
| **G42-03** minor: six proofs of 40 lines or more lack step comments (policy §3; the documentation part of SY-F09) | **LE-steps** `355a0288`: `-- Step k:` comments at the major blocks, tied to the existing sketches | `le-r2.txt` § LE-steps, `steps-r2.txt`, `frozen-r2.txt` | § 3: comment-only; accurate against the proofs and sketches; closed? |

## What to check

### 1. G42-01: LE-reuse-2 is a proof-only reuse through the published readers

The edit, verbatim (`git diff e9b03c43 26f0b77b`; the only file is `Yao/HybridProof/RunWithHost.lean`):

```lean
 /-- The one-bit acceptance test `w ↦ [acc w]` is polynomial-time.
+Reuses `StateLoop.MajLoop.acc_poly`.
 `PolyTimeComputable fun w => [acc w]`. -/
-theorem acc_poly : PolyTimeComputable fun w => [acc w] :=
-  polyTimeComputable_isNil.comp
-    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
+theorem acc_poly : PolyTimeComputable fun w => [acc w] := by
+  have hacc : ∀ w, acc w = Complexity.StateLoop.MajLoop.acc w := fun w =>
+    (acc_eq w).trans (Complexity.StateLoop.MajLoop.acc_eq w).symm
+  have hfun : (fun w => [acc w]) = fun w => [Complexity.StateLoop.MajLoop.acc w] :=
+    funext fun w => congrArg (fun b : Bool => [b]) (hacc w)
+  rw [hfun]
+  exact Complexity.StateLoop.MajLoop.acc_poly
```

- **Proof-only** (`checks/le-r2.txt`, `checks/decls-r2.txt`). The imports are byte-identical. All 9 declarations of
  the file keep their names, order and headers; the header of `acc_poly` (keyword to the top-level `:=`) is unchanged.
  Outside `acc_poly`'s span (docstring to the next blank line) the file is byte-identical. The docstring gains one
  line, the disclosure; its formula line is kept. Across all 70 PR files, `RunWithHost.lean` is the only file whose
  code differs after stripping comments, and only inside `acc_poly`.
- **What the new proof reads.** Its names: `acc`, `acc_eq` (this file's own definition and its `rfl` reader),
  `Complexity.StateLoop.MajLoop.acc`, `MajLoop.acc_eq`, `MajLoop.acc_poly`, `funext`, `congrArg`, `Eq.trans`/`symm`.
  It has no `unfold`, `delta`, `simp`, `dsimp`, `show`, `rfl`, `decide`, `change` or cast; the one rewrite is
  `rw [hfun]` with the local equation `hfun`. The two acceptance tests are identified pointwise through the two
  readers only.
- **The reused lemma** (`TCSlib/Complexity/Randomized/Build/StringLoops.lean`, `checks/closure-r2.txt`): `acc` at
  line 97, `acc_eq` at 100, `acc_poly` at 144. The two predicates are the same (`decide (pairFstD (pairSndD x) = [])`
  after renaming the bound variable). `StringLoops.lean` is the same blob at `f9fda8fe`, the pin, the head and in
  round 1's `sources.zip`. The import chain is `RunWithHost` → `Complexity/Randomized/Repetition` → `StringLoops`,
  so no import is added and the source closure keeps its 262 paths.
- **Not round 1's candidate body.** Round 1 proposed `simpa only [acc_eq, Complexity.StateLoop.MajLoop.acc_eq] using
  Complexity.StateLoop.MajLoop.acc_poly`, and the resolutions said "or the nearest form that elaborates". The commit
  uses the `Eq.trans`/`funext` form above and keeps the candidate as "Fallback 1" in its message (`le-r2.txt` quotes
  the message without its trailer lines). The committed body elaborated on M′, so no fallback was tried.
- **On M′** (`checks/integration-r2.txt`): `RunWithHost` rebuilds with rc 0 and 0 errors, as do all 20 modules
  downstream of the 9 changed files. `#print axioms` gives `RunWithHost.acc_poly` and `MajLoop.acc_poly` the
  standard three; `#admitted` finds no `sorryAx` user in `acc_poly`'s closure (4610 constants). `#check` prints
  the unchanged statement and both readers, each `acc w = decide (pairFstD (pairSndD w) = [])`. The closures of
  `yaoHybrid_polyTime`, `yaoHybrid_hbcSecure` and `yaoProtocol_hbcSecure` grow by 4 constants each (9168 → 9172,
  20475 → 20479, 21453 → 21457).
- **Rule 10 on `RunWithHost.lean` at M′**: coe A (canonical), strict A, coe B and strict B, 844/844/845/845
  requests, 0 errors each, install and EOF records present. `Complexity.StateLoop.MajLoop.acc` is a sealed row in all
  four, and the collector names `acc_poly` as its only term reader. Each probe is bound to the head: removing the
  recorded insertions (each hash checked) gives `RunWithHost.lean` at `355a0288` byte for byte. Its hash equals the
  manifest's `probe_sha256` and the run record's.

Is LE-reuse-2 proof-only, does it read `MajLoop.acc` only through the published readers (no unfold of either `acc`),
are the statement and the imports unchanged, and is the disclosure adequate? Does it close G42-01?

### 2. G42-02: LE-refs is comment-only, and the entries are right

- `ChunkScanner.lean` and `GarblingProgram.lean`: one pure insertion each, every inserted line inside the module
  docstring `/-! … -/`. Each file is identical after stripping comments, and removing the inserted lines restores the
  parent byte for byte (`le-r2.txt`). The entries, as inserted:

  ```text
  * [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
    Cambridge University Press, 2009, §6.2 (descriptions of uniform circuit families).
  * [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*,
    STOC 1990, pp. 503–513 (point-and-permute row order of the garbled tables).
  ```

- **Tags against `## References`** over the 70 files (`sources-r2.txt`): round 1 had 2 tags without an entry (the
  two of G42-02); round 2 has 0. The AB09 entry repeats `DescriptionDecoder.lean`'s word for word. The BMR90 entry
  has the bibliographic data of the existing entries in `Yao.lean`, `RowFromCoins.lean` and `CoinRelabel.lean`. Those
  entries are listed beside the new ones. As in round 1, AB09 is in the tag registry (`sources.json`), BMR90 is not,
  and BMR90 has no transcription at the pin.

Are the two entries correct and complete, and does LE-refs close G42-02?

### 3. G42-03: LE-steps is comment-only, and the step comments are accurate

- Six files, 56 inserted lines, all pure insertions. Every inserted line is a `-- ` line comment at the indentation of
  the next code line. Removing them restores each parent byte for byte, and each file is identical after stripping
  comments (`le-r2.txt`). The sketches (docstrings) of the six proofs are unchanged since round 1.

  | Proof | File | Step comments | Head lines |
  |---|---|---|---|
  | `yaoHybrid_polyTime` | `Yao.lean` (inside the approved body region) | 8 | 865–974 |
  | `acceptProb_fill` | `SelectedLaw.lean` | 7 | 83–157 |
  | `exists_data` | `FakeSimulatorFactory.lean` | 3 | 91–141 |
  | `pick_iff_place` | `SeedCoordinates.lean` | 4 | 250–301 |
  | `tables_poly` | `FakeProgram.lean` | 7 | 254–325 |
  | `outputBit_poly` | `BobIO.lean` | 6 | 100–144 |

- `checks/steps-r2.txt` prints, for each proof, its `**Proof sketch.**` and its step comments with their head line
  numbers. It also locates every backticked name of a comment in that proof's code. All of them occur there
  (`HybridProtocol.polyTime_iff`, `outLen`, `e`, `c`, `pick`, `place`, `e.prodCongr c`,
  `CoordinateSwap.acceptProb_swap`, `Sum.inr`, `NonceCoordinates.pick_iff_place`, `hgs`, `tableWordWith_congr_at`,
  `outputBit_eq`); `(i, t)`, `inA + i`, `y_i`, `(u, true)` and `[outputBit z]` are notation, not names.
- The unnecessary-`simpa` linter warning of `BobIO` moved from line 211 to 218 (the comments above it); it remains
  informational.

Do the comments describe the code that follows them, agree with the sketches, and mark the major blocks (policy §3)?
Does LE-steps close G42-03?

### 4. `Yao.lean`'s frozen regions

`checks/frozen-r2.txt` repeats round 1's check at the new head, against the tip `f9fda8fe`:
- It masks the six approved regions and LE-title's title line at the tip and the head. Everything outside them is
  byte-identical (0 violations, 0 rule breaks), and each of the 7 unmasked hunks lies inside one region on both sides.
- The 76 declarations are in the same order with byte-identical headers and definitions. Only the two targets'
  docstrings differ, and their statement prose before `**Proof sketch.**` is byte-identical. `yaoSeed_good_whp` is
  unchanged, and one import is added.
- The six controls behave as in round 1.
- `Yao.lean` has **1195 lines** (≤ 1,200, SY-2; round 1: 1179), max width 99.
- **Round 1 → round 2:** 8 pure insertions, all inside the `yaoHybrid_polyTime` body region (128 → 144 lines), whose
  code is identical after stripping comments. The sketch is unchanged, and the masked files are equal.
- `Uniform.lean` is the same blob as in round 1; `DAGCircuit.lean` is unchanged against the tip.

Do the six regions plus LE-title still hold?

### 5. Everything else is unchanged (`decls-r2.txt`, `le-r2.txt`, `lint-r2.txt`)

- **Declarations:** 856 across the 70 files in both rounds, the same names in the same order. No header or definition
  block differs. The only declaration docstring that differs is `acc_poly`'s; the module docstrings that differ are
  `ChunkScanner`'s and `GarblingProgram`'s. There is no new name, so there is nothing new to scan for duplication.
- **Admissions:** 0 `sorry` tokens outside comments in the 70 files, in both rounds.
- **Widths:** every line of the 70 files is at most 100 characters.
- **Controls** (`le-r2.txt`): on each commit's first file, an added tactic, a doubled space and an inserted code line
  are each caught.
- **Lint.** `scripts/campaign_style_lint.py TCSlib --check8b` ran over the 70 files at both heads, in mini trees
  written from git objects. Every check is per file, and the two facades' child directories hold only PR files, so
  these lines are the whole-tree run's lines for these files. Both runs give 0 FAIL and the same 2 WARN:
  `Uniform.lean`'s inherited check-8 `IsPUniform`, and `Yao.lean`'s size WARN, whose count moves from 1179 to 1195.

### 6. The integration evidence (M and M′)

`briefs/pass-shelat-ch5-8/fills/sc-yao/final-r1/integration-tip/` at the pin: README, `SHA256SUMS` and
`integration-tip-evidence.zip` (SHA-256 `4d24501bca1d67a8cf8905448acb77b161a61a45e8d38f72f14dea2fca95d6d8`, 989
entries). The ZIP is not copied. All 989 entries verify against `SHA256SUMS`, with an exact path set
(`checks/integration-r2.txt`). `verification-r2.zip` holds byte copies of the cited entries.

- **The merges.** T is round 1's records pin `f22e0f67`, whose code is the current pin's.
  - **M** = T merged with `e9b03c43` (`e327a5f2`, tree `741bafe2`).
  - **M′** = T merged with `355a0288` (`061ad60c`, tree `84c5381b`).

  Both are local scratch commits, not pushed. `git merge-tree --write-tree` reproduces both trees.
  - M′'s tree differs from M's exactly by `git diff --raw e9b03c43 355a0288` (9 paths).
  - Over `TCSlib`, `TCSlib.lean` and `audits`, M′ differs from `201bf57a` exactly by `f9fda8fe..355a0288` (70 paths).
  - The ZIP's raw diffs equal these.
- **M build** (incremental on `dl-oleans-2` from the snapshot base `eff2dcd0`):
  - 772/772 modules rc 0 with 0 errors, root `TCSlib` and both `audits/*/Checks` included. The built set is the
    downstream of every module changed since `eff2dcd0` in M's tree, recomputed here.
  - Every record's source hash equals its blob in M.
  - State check 1410/1410, RESULT OK. Every olean is byte-identical to a reference build.
- **M′ build** (on M's built state):
  - The 20 rebuilt modules are exactly the modules whose import closure meets the 9 changed files (recomputed
    here). They gave 20/20 rc 0, 0 errors, 0 `sorry`, and one warning (`BobIO`'s `simpa`).
  - The sources are bound to M′'s blobs, and the logs to their records.
  - State check 1410/1410, RESULT OK.
- **Admissions:** 229 at the tip, **227** at M and at M′, equal per module. The only change is `Yao` 2 → 0, and
  the 68 new modules have none.
- **Axioms.**
  - At M′: `yaoProtocol_hbcSecure`, `yaoHybrid_polyTime`, `yaoHybrid_simulators`, `yaoHybrid_hbcSecure`,
    `yaoSeed_good_whp`, `hbcSecure_compose` and `acc_poly` use `propext, Classical.choice, Quot.sound`. No closure has
    a direct `sorryAx` user.
  - **`yaoProtocol_hbcSecure` is now standard.** In round 1 it reached `sorryAx` only through the then-unmerged
    `hbcSecure_compose` (#324, merged as `201bf57a`).
  - At M, `AxiomsTipExtra` also gives the ten `otProtocol_*` results the standard three.
  - The owners' census is 1492 stored constants, all standard; its `AX` rows are identical at M and M′.
- **Seals.**
  - **`Yao.lean` was sealed at M**, where it is `e9b03c43`'s file: coe A 3046 requests, 0 errors; coe B 3047
    requests, 24 errors in the same 9 declarations as round 1. Both logs are byte-identical to Phase 2's after the
    probe-directory rename.
  - These seals were **not re-run at M′**. There, `Yao.lean` differs only by LE-steps' 16 comment lines in the
    `polyTime` body (§ 3, § 4).
  - **`RunWithHost.lean` was sealed at M′** in all four variants (§ 1).
  - The other seven files of LE-refs and LE-steps (`BobIO`, `ChunkScanner`, `FakeProgram`, `FakeSimulatorFactory`,
    `GarblingProgram`, `SeedCoordinates`, `SelectedLaw`) were **not re-sealed**. Their changes are comment-only, and
    round 1's coe-A 68/68 helper seals are at `e9b03c43`.
- **Restore:** `dl-oleans-2` back to snapshot `457ba704…`, SNAPSHOT EQUAL (rechecked independently).

Does the evidence bind to the head, and does it show no regression? Is it sufficient given that `Yao.lean` and the
seven comment-only helpers were not re-sealed at M′? Or is a re-run necessary? Missing necessary evidence would be a
major.

### 7. The round-1 confirmations

The only code change since round 1 is `acc_poly`'s body, with its statement unchanged; everything else is comments
(§ 5). Round 1 confirmed the following; say whether each still holds:
1. **Efficiency.** `yaoHybrid_polyTime` supplies both efficient strategies, both call-input machines and the
   answer-independent envelope through `HybridProtocol.polyTime_iff`, for arbitrary words and histories. The decoder
   is correct on canonical descriptions and polynomial on all strings, and the evaluator handles arbitrary tables and
   answers. The fixed enumerations are finite constant-arity branches. `acc_poly` feeds this through
   `RunWithHost.exists_machine`.
2. **Statistical simulation:** the copying simulator and Bob's output switch both rest on `yaoSeed_good_whp`'s bad
   event and `yaoHybrid_correct`, with tape equivalences on the actual tape words.
3. **Exact endpoints:** `CoinSeedRelabel.seed_relabel`, `BobStageZero.acceptProb_eq_stage0` and
   `SamplerEndpoints.acceptProb_end_eq_ideal`, with no uniform-permutation substitution.
4. **The B1 embedding and Gate 27's obligations (1)–(5):**
   - the all-occurrence enumeration, and both slice shapes (`0 + n + n = 2n`; `2n + n + (4n + 2) = 7n + 2`);
   - identical advice, symbolic label separation, pointwise reconstruction;
   - polynomial-time `rebuild_poly`, and bounded advice;
   - non-adaptive challenges.
5. **Quantifiers and total error:**
   - The simulators are fixed before the distinguisher.
   - There is one worst advice option per parameter, with the averaging back by `SelectedLaw.acceptProb_fill`.
   - The total error is $\delta(n) + 2S(n)\lvert\mu(n)\rvert$.
   - The edge cases add no hypothesis.
6. **The source:** agreement with the Lindell–Pinkas proof architecture; the deviations are documented; no fabricated
   tag or PS10 locator.
7. **Frozen files and landing edits:**
   - `Yao.lean`'s 76 declarations and regions;
   - `Uniform.lean`'s seven readers;
   - `DAGCircuit.lean` unchanged;
   - the 68 other paths, which are the hub and its helpers;
   - LE-bullet, LE-reuse, LE-title and LE-doc;
   - docstrings on all 739 new public declarations.
8. **Rule 10 and the build:**
   - `Yao.lean` seal A 0. Seal B has 9 new errors, attributed to `PolyExpr.eval`.
   - `Uniform.lean`'s 4 inherited errors.
   - Helpers coe-A 68/68, and the paired controls.
   - The explicit-unfold scan finds 0 foreign unfolds.
   - The build: 718/718.
   - The axioms of the four Yao results.
9. **The SY-F grades:**

   | Item | Grade |
   |---|---|
   | SY-F01 | Resolved |
   | SY-F02 | DL-51 |
   | SY-F03 | DL-49 extended |
   | SY-F04 | Fixed |
   | SY-F05 | Fixed; remainder DL-52 |
   | SY-F06 | Regraded to G42-01 |
   | SY-F07 | Note |
   | SY-F08 | Note |
   | SY-F09 | Regraded to G42-03; the linter warning is a note |
   | SY-F10 | Note |
   | SY-F11 | Note |
   | SY-F12 | Size exception, now 1195 ≤ 1,200 |

### 8. Is anything new undisclosed?

Everything that is new since round 1:
- the three commits;
- the integration evidence (`ed0d2acc`);
- the updated PR description (`pr-description-r2.md`, below);
- the records commits after `f22e0f67`.

Is any change, claim or omission among them undisclosed? The known slips are listed below.

## Merge interaction (maintainer merge conditions, not audit items)

`checks/mergetrees-r2.txt`:
- `git merge-tree --write-tree` of the head with the pin is clean. The merged tree differs from the pin in exactly
  the PR's 70 paths, and its code subtrees equal M′'s.
- With each open PR on the records branch the merge is clean, and no path is shared with #341's 70:
  - #331 `9e7a9648`;
  - #338 `d45d3682`;
  - #339 `839f36cc`.
- #340, which round 1 tested, is no longer open.

## Known dispositions and slips (not findings)

- **The body is not round 1's candidate** (§ 1). The candidate is Fallback 1 in the commit message, untried.
- **M′ is T × `355a0288`, not M × `355a0288`.** The decision-log row and the PR description say "M′ = M merged
  with `355a0288`" and "M′, M with `355a0288`". The integration README and the merge facts give the parents T and
  `355a0288`. The trees are related exactly as § 6 states, and the build ran incrementally on M's built state.
- **Signatures.** The integration README says the three signatures are "not verifiable here", since no
  `allowedSignersFile` is configured. `checks/series-r2.txt` verifies them with the public key in each signature. The
  key is the same one that signs the records pin, and a tamper control fails. `%G?` prints N for the same reason.
- **The PR description** (`pr-description-r2.md`, fetched at staging with the GitHub MCP tool and the REST API; the
  same text):
  - "Helpers: canonical coe-A seals pass on all 68" is round 1's evidence at `e9b03c43`. At `355a0288` only
    `RunWithHost` was re-sealed (§ 6).
  - It still abbreviates `Complexity/CircuitComplexity/Uniform.lean` as `Circuits/Uniform.lean`.
  - It says round 2 is "being staged".
  - The REST `base.sha` is `f22e0f67`; records commits only have landed since.
- **The landing-edit checks recorded in the decision log** were run without Lean and not filed as evidence: docstrip
  CODE-EQUAL and byte removal restoring the parent. `le-r2.txt` reproduces them from git objects. The resolutions
  named `RunWithHost`'s canonical coe-A seal and "its strict and coe B seals"; all four variants were run.
- **The pin is one records commit past the integration commit `ed0d2acc`.** `2da7e0f3` adds the decision-log row that
  records the PR description update and the start of this staging.
- **Phase 2's raw seal directories were deleted** after the integration job checked that every file is in the
  committed `review-evidence.zip` with the same hash (integration README § Space). Round 1's pack points to that ZIP.
- **Lint.** It was not re-run over the whole tree for round 2; `lint-r2.txt` covers the 70 files (§ 5).

## Evidence files

- **`resolutions-r1.md`** and **`findings/`**: the round-1 dispositions and findings (records, at the pin).
- **`pr-r2.diff.txt`**: `git diff e9b03c43..355a0288`. It has 9 files, 69 insertions and 3 deletions (SHA-256
  `bdd6717d…`), and equals the three commits' diffs together.
- **`pr.diff-r2.txt`**: `git diff f9fda8fe..355a0288`. It equals `git diff 2da7e0f3...355a0288` byte for byte, with
  70 paths, 15879 insertions and 67 deletions (SHA-256 `e4dd3634…`).
- **`source-head-r2.json`**: the head, base, pin and round-1 head. It gives the 9 paths changed since round 1, and for
  each of the 70 files its status, SHA-256, line count and over-width count (none over 100 characters).
- **`sources-r2.zip`**: the 9 files changed since round 1, at the head. The source closure at the head has round 1's
  262 paths; 253 of them are byte-identical to round 1's `sources.zip` (`105be989…`, records `gates/42-sc-yao/`), and
  the other 9 are these. The ZIP's `README.md` says so, and `checks/closure-r2.txt` checks it. `PS10/` is unchanged.
- **`verification-r2.zip`** (71 entries). `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each one's
  source.
  - `checks/`: `series-r2`, `le-r2`, `decls-r2`, `frozen-r2`, `steps-r2`, `sources-r2`, `integration-r2`,
    `closure-r2`, `mergetrees-r2` and `lint-r2`, generated from git objects and the committed integration evidence.
    Nothing was built and no Lean ran. Their scripts are in `checks/tools/`.
  - `integration-tip/`: the README and `SHA256SUMS` (byte copies at the pin); `POINTER.txt` (the ZIP's path, size,
    SHA-256 and entry count); and `entries/`, 44 cited entries, each equal to its manifest row. These are the merge
    facts and raw diffs, the M′ plan, build records and logs, the state update, the censuses, the axiom summaries, the
    `AxiomsLE` probe and log, the seal summaries, manifests and run records, M's build summary, the Phase 2
    comparison, and the restore check.
  - `records/`: the round-1 findings (with their `SHA256SUMS`), the resolutions, the round-1 dispatch and records
    `SHA256SUMS`, the plan, and `decision-log-sc-yao.md`, the extract of its rows 816–829.
  - `pr/pr341-rest-fields.json`: the REST fields the checks read.
- **`pr-description-r2.md`**: #341's description as it stands, fetched at staging, raw `.body`.
- **Round 1:** `outbox/gates/42-sc-yao-gate/` on the exchange at `747b61e7d95d44461639c5884aed33aa4908fc00`, with
  records `f22e0f6798815b9263893e61928b4f16452f74ee`. `pack.md` here is its pack. The policy, the brief, rulings SY-1
  to SY-6, the ledger rows and the PS10 excerpt are unchanged since then.

## Findings delivery

Return `gate42-sc-yao-r2-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP. Use
round 1's table and severities.
- Say for each round-1 finding whether it is closed.
- Say whether the round-1 confirmations still hold.
- Name anything new.
- Report the audited head and the counts by severity.

The gate closes at zero blockers and zero majors.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** any of the following:
  - a changed frozen statement;
  - a forbidden read in a touched declaration not covered by the rulings;
  - an undisclosed copied private lemma, or an undisclosed re-proof of a public one, outside the ledger rows and
    rulings in force;
  - a fabricated source tag;
  - necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, proof sketch, step comment or
  citation.
- **note:** anything else.
