## ===== briefs/pass-shelat-ch5-8/gates/42-sc-yao/pack-r2.md (this pack) =====

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

## ===== briefs/pass-shelat-ch5-8/gates/42-sc-yao/resolutions-r1.md (records, at 2da7e0f3cd65ec93ed71813b7828c3b66ba18942) =====

# Gate 42 · resolutions, round 1 · HOLD → landing edits

Codex's verdict is **HOLD**: 0 blockers, 1 major, 2 minors, 0 notes.
- **Findings:** `findings/gate42-sc-yao-findings.md`, SHA-256
  `e1076c1e4f643c066106754c0eb02d8d3426b371de47ba698dcecb5504eabdcb`.
- **Audited:** #341 at `e9b03c437aca251846430ff23b40ee5ff3d3347a`; records `f22e0f67`, with the later rulings `67423db6`,
  `d6fe1ddd` and `bf08dbfa`; exchange `747b61e7`.

Codex found **no mathematical gap** in the two frozen targets. It confirmed:
- the efficiency proof, the statistical simulation, the exact endpoints, all five Gate 27 obligations, and the
  quantifier order and total error `δ(n) + 2S(n)|μ(n)|`;
- agreement with the Lindell–Pinkas proof architecture;
- frozen-file integrity, including `Yao.lean`'s six regions plus LE-title and `Uniform.lean`'s seven readers;
- the landing edits LE-bullet, LE-reuse, LE-title and LE-doc;
- Rule 10, the build and the axioms.

SY-F01 to SY-F05 are resolved or accepted under the rulings, with DL-49, DL-51 and DL-52 confirmed against the code.
SY-F06 and SY-F09 are regraded, to G42-01 and G42-03.

| Finding | Grade | Resolution |
|---|---|---|
| G42-01 | **major** | **LE-reuse-2**, proof-only. `RunWithHost.acc_poly` (`RunWithHost.lean:88`) re-proves the public `Complexity.StateLoop.MajLoop.acc_poly` (`Complexity/Randomized/Build/StringLoops.lean:144`) for the same predicate. Its body becomes Codex's candidate: `simpa only [acc_eq, StateLoop.MajLoop.acc_eq] using StateLoop.MajLoop.acc_poly`, or the nearest form that elaborates, reading only the two published readers. There is no import change, since `RunWithHost` already reaches `StringLoops` through `Repetition`. The statement and the helper API are unchanged. No ledger row is needed. |
| G42-02 | minor | **LE-refs**, docstrings only. Full `[AB09]` entry in `ChunkScanner.lean`'s `## References`; full `[BMR90]` entry (Beaver, Micali, Rogaway, "The round complexity of secure protocols", STOC 1990) in `GarblingProgram.lean`'s. |
| G42-03 | minor | **LE-steps**, comments only. Step comments at the major proof boundaries, tied to the existing sketches, in: `yaoHybrid_polyTime` (`Yao.lean:863`, inside an approved body region); `SelectedLaw.acceptProb_fill`; `FakeSimulatorFactory.exists_data`; `SeedCoordinates.pick_iff_place`; `FakeProgram.tables_poly`; `BobIO.outputBit_poly`. Statements and proof terms are unchanged. |

**Checks for the new head:**
- LE-refs and LE-steps are comment-only after stripping comments.
- LE-reuse-2 touches only `acc_poly`'s body.
- The frozen check of `Yao.lean` still passes, with the six regions plus LE-title.
- Built incrementally on the integration tree with the current tip:
  - the changed modules and their downstream give rc 0 with 0 errors;
  - the four Yao results and `yaoProtocol_hbcSecure` use standard axioms only;
  - `RunWithHost`'s canonical coe-A seal passes, and so do its strict and coe B seals.

Then Gate 42 round 2 (Codex) at the new head.

## ===== briefs/pass-shelat-ch5-8/gates/42-sc-yao/findings/gate42-sc-yao-findings.md (records, at 2da7e0f3cd65ec93ed71813b7828c3b66ba18942) =====

# Gate 42 — sc-yao proof audit

**Verdict: HOLD — one major duplication finding and two documentation minors.**

| Severity | Open findings |
|---|---:|
| Blocker | 0 |
| Major | 1 |
| Minor | 2 |
| Note | 0 |

Audit of [draft PR #341](https://github.com/Shilun-Allan-Li/tcslib/pull/341), conducted on 16 November 2026. The accepted exceptions and resolved historical findings below are not counted again as open findings. Dispatch and merge remain with Seyoon; the separately running integration build remains a maintainer merge condition.

## Pins and method

| Material | Commit |
|---|---|
| Exchange pack | `747b61e7d95d44461639c5884aed33aa4908fc00` |
| Audited Lean head | `e9b03c437aca251846430ff23b40ee5ff3d3347a` |
| Campaign records | `f22e0f6798815b9263893e61928b4f16452f74ee` |
| SY-F01–03 rulings | `67423db6c9d6448ae531b04f42c315585d00d502` |
| DL-49 wording correction | `d6fe1ddd4f38b9bd29d2c707dcb4b60129b4586e` |
| SY-F05 remainder / DL-52 | `bf08dbfa3a057a3b41d20f6dbede3066bc5e6660` |

I independently checked the pack's 22 SHA-256 entries, all 248 manifested entries of `verification.zip`, and all 1,510 manifested entries of the separately retrieved review-evidence ZIP, including exact archive path sets. Its SHA-256 is `d3f7c3da0d081acd9275e798514fffd7b538c83787a109c11c59bab4e2c3b5a8`. All 103 bundle sections match their named source blobs/files, allowing the bundle's separating newlines. All 262 Lean files in the supplied source closure match Git blob identities at the audited head. The supplied PR diff matches an independently generated diff, fixing Git's hash abbreviation width.

The worker's 7,597-entry top-level manifest has exactly the committed delivery's path set. The pack's full worker-byte verification records were inspected; this audit did not independently stream every worker blob again. I reviewed the proof chain and recounted the supplied build, axiom and seal evidence; **I did not run a fresh Lean build or new seals**.

## Open findings

Helper paths below are relative to `TCSlib/Cryptography/SecureComputation/Yao/HybridProof/`.

| ID | Severity | File / declaration | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G42-01 | **major** | `RunWithHost.lean:88` `acc_poly` | This re-proves public `Complexity.StateLoop.MajLoop.acc_poly` (`TCSlib/Complexity/Randomized/Build/StringLoops.lean:144`) for exactly the same word predicate. The predicates at `RunWithHost.lean:69` and `StringLoops.lean:97` both return `decide (pairFstD (pairSndD w) = [])`; their public readers identify the functions pointwise. The new body re-assembles the same polynomial-time proof from `polyTimeComputable_isNil` and pair projections. `StringLoops.lean` and `Repetition.lean` are byte-identical between the issue base and the head, and `RunWithHost` already imports `Repetition`, which imports `StringLoops`. Thus SY-5 does not apply and no extra import is needed. The REPORT does not disclose `MajLoop`; DL-49/51/52 and the later rulings do not cover this overlap. SY-F06 mentions the predicate coincidence but misses the matching public efficiency theorem. | Preserve the helper API and derive `acc_poly` from `MajLoop.acc_poly` through the two public readers, then refresh the required checks. Alternatively, obtain an explicit ruling accepting this exact duplication as ledger debt. |
| G42-02 | minor | `ChunkScanner.lean:28`; `GarblingProgram.lean:27` | The first module's references section uses `[AB09, §6.2]` without a full AB09 bibliography entry. The second cites `[BMR90]` in `tables_poly`'s docstring, but its references section lists only PS10. These are bibliography omissions, not fabricated tags. | Add the full AB09 and BMR90 references to the respective module docstrings. |
| G42-03 | minor | `Yao.lean:863` `yaoHybrid_polyTime`; `SelectedLaw.lean:69` `acceptProb_fill`; `FakeSimulatorFactory.lean:83` `exists_data`; `SeedCoordinates.lean:239` `pick_iff_place`; `FakeProgram.lean:227` `tables_poly`; `BobIO.lean:99` `outputBit_poly` | These six proofs have at least 40 proof lines and no internal step comments. Their sketches exist, but the brief's “long proofs get step comments” requirement and policy §3 also require comments connecting major proof blocks to those sketches. This is the unresolved documentation component of SY-F09. | Add brief comments at the proof's major boundaries. Keep statements and proof terms unchanged. The unnecessary-`simpa` warning remains informational. |

A proposed proof-only replacement for G42-01 is below. It uses the existing import closure and published readers, preserving the statement. This candidate was not elaborated in this audit:

```lean
theorem acc_poly : PolyTimeComputable fun w => [acc w] := by
  simpa only [acc_eq, Complexity.StateLoop.MajLoop.acc_eq] using
    Complexity.StateLoop.MajLoop.acc_poly
```

This finding concerns reuse discipline, not the mathematical validity of the current efficiency proof. No mathematical gap in the two frozen targets was identified.

## Proof assessment

1. **Efficiency.** `yaoHybrid_polyTime` supplies both efficient main strategies, both call-input machines and the answer-independent message envelope through `HybridProtocol.polyTime_iff`. The strategy contracts quantify over arbitrary words and histories. The description decoder is correct on every canonical circuit description and polynomial-time on all strings. The evaluator handles arbitrary received table/answer words, with a polynomial bound on every encoded prefix state. Fixed assignment enumerations are handled by finite, constant-arity branches; no efficient computation of `Finset.univ.toList` is assumed.

2. **Statistical simulation.** The copying simulator for Alice and the output switch for Bob use the same bad-seed bound from the unchanged `yaoSeed_good_whp`. The two components of `yaoHybrid_correct` supply the required outputs off that event. Tape equivalences preserve the actual tape words, and unused independent tapes are removed through published marginal identities.

3. **Exact endpoints.** `CoinSeedRelabel.seed_relabel` and `BobStageZero.acceptProb_eq_stage0` transport the entire tape, including unused coordinates and XOR shifts. `SamplerEndpoints.acceptProb_end_eq_ideal` identifies the last stage with the fixed fake simulator. The proof does not replace the actual row-order distribution by a uniform permutation distribution.

4. **B1 embedding / Gate 27 obligations.** `GateOccurrences` enumerates selected inactive-key occurrences across all gates and proves exhaustion, uniqueness and the four-per-gate bound. `SelectedRows` implements both slice shapes: the only/inner case fits because `0 + n + n = 2n`; the outer case fits because `2n + n + (4n + 2) = 7n + 2`. `SelectedStep.advice_next` fixes identical advice on both sides. Acyclicity, distinct gate arguments and sink outputs supply symbolic label separation. `SelectedTables` proves pointwise reconstruction, and `SliceReconstruction.rebuild_poly` supplies a total polynomial-time reconstruction. `SelectedAdviceBounds` bounds all retained advice. All five Gate 27 obligations are discharged; no adaptive ciphertext-dependent challenge messages are required.

5. **Quantifiers and total error.** Both simulator machines are fixed before the distinguisher. `SliceReduction.reconstruction_negligible` selects one worst finite advice option per parameter, producing one negligible bound covering every input, selected substep and baseline tape. `SelectedLaw.acceptProb_fill` justifies averaging back to the actual tape law. The gate chain and `simulators_of_output_switch` yield the bound

   \[
   \delta(n)+2S(n)\lvert\mu(n)\rvert,
   \]

   negligible by the published closure lemmas. Empty circuits use the optional empty advice choice and require no selected wire. Zero key width, empty input/output lists, zero/one/two-argument gates, repeated sink outputs, unused coordinates and coincident key values introduce no extra hypothesis. A repeated argument within one gate is excluded by the frozen fan-in predicate; a wire used at different positions in different gates is covered by the all-occurrence construction.

The proof establishes the frozen OT-hybrid statements. Its fake-garbling/topological-hybrid architecture agrees with the cited [Lindell–Pinkas proof, pp. 180–184](https://www.cs.columbia.edu/~tal/6261/SP16/LP_yao.pdf). The PS10 excerpt supports Protocol 162.6, Definition 155.1 and Theorem 163.7. Bit transfer, XOR row order, sink outputs, output decoding and the joint PRF hypothesis remain explicitly documented deviations. No fabricated new source tag or PS10 locator was identified; the `.a` locators are the disclosed inventory labels for unnumbered source passages.

## Frozen files and landing edits

- `Yao.lean`: all 76 declarations remain in order. Outside the six approved regions and LE-title, the file is byte-identical to the base. Target headers, statement prose, `include` prefixes and `yaoSeed_good_whp` are preserved. The head has 1,179 lines, within SY-2's 1,200-line cap.
- `Uniform.lean`: removing exactly the seven approved formula-docstring `rfl` readers restores the base byte for byte. No attributes are attached to them. `DAGCircuit.lean` is unchanged against the tip.
- The other 68 changed paths are the new hub and its helpers. The hub imports its 67 children. No additional frozen file changes.
- LE-bullet and LE-title have their stated scope. LE-reuse derives the two assignment-fold results directly from `GarblingProbability.assignmentFold_small`, preserving their headers and imports. Independently stripping comments from all 64 LE-doc files gives identical code before and after the commit.
- All 739 new public declarations have docstrings. No further material formula or sketch mismatch was identified. G42-02 and G42-03 remain documentation cleanup items.

## Rule 10 and build evidence

| Check | Audited evidence / result |
|---|---|
| `Yao.lean`, seal A | 0 errors, coe and strict. |
| `Yao.lean`, seal B | 24 errors in each variant; 15 inherited and 9 new. The new 2 efficiency and 7 simulator-body errors are `PolyExpr.eval` index/type conversions or their cascades. No additional forbidden read was identified. |
| `Uniform.lean` | The same 4 errors in the same two inherited declarations at base and head; the new readers pass. |
| Helpers | All 68 canonical coe-A seals pass; all 15 sampled other-variant seals pass. The recorded 272 worker seals support the wider coverage. |
| Probe identity | Independently removing the seal harness reproduces the audited code of all 71 canonical probe owners, modulo comments and blank lines. |
| Controls | Independently recounted: coe 83/83 negative declarations fail once, 15 unsealed files pass; strict 100/100 negatives fail once, 17 unsealed files pass. The strict `ctlCoeReader` failures are exactly the recorded projection-coercion harness effect. |
| Explicit reads | Reviewed the 1,512-reference scan and its 28 local-name candidates; no uncovered foreign-definition unfold identified. |
| Build | Recounted 718/718 successful module checks with 0 `error:`/`error(` diagnostics; checked raw-log hashes against run records. The recorded whole-order check is 1,356/1,356. |
| Axioms | The three audited Yao results and `yaoSeed_good_whp` report only `propext`, `Classical.choice`, `Quot.sound`, with no direct `sorryAx` user in their closures. The recorded 1,492-constant census has no nonstandard axiom. |

The old build's `yaoProtocol_hbcSecure` admission is traced solely to then-unmerged `hbcSecure_compose`. It does not hold this OT-hybrid audit. The integration build with #324/#327 remains outside the audit, as instructed.

## SY-F01–SY-F12 grades

| Item | Grade / disposition | Reason |
|---|---|---|
| SY-F01 | Resolved by confirmation | The four approved imports serve range assembly, `dbl_append`, the expectation coupling inequality and the encoding identity. Their uses match the recorded requests; no additional unapproved helper import was identified. |
| SY-F02 | Accepted debt, DL-51 | The named statistical-switch declarations and DDH relative match the code. Without the ruling, the undisclosed re-proof would be major, not minor. The ruling permits promotion and re-pointing later. |
| SY-F03 | Accepted debt, DL-49 extension | Both `encodeMsgs_eq_encWords` copies and the flat-map relative match. The two proofs/statements agree up to bound-variable names; their docstrings differ. Apply the wording correction. Without the ruling, the undisclosed overlap would be major. |
| SY-F04 | Fixed | LE-doc is comment-only; formula coverage is restored. G42-02 concerns separate file-level references. |
| SY-F05 | Fixed / accepted debt | Assignment-fold reuse is fixed. DL-52 correctly records `OTAnswerWords.length_answersB:41` / `answersA_nil:94` against #324's `length_answersB:60` / `length_answersA:52`, using output lengths one and zero. Re-point after #341 merges, per the later ruling. |
| SY-F06 | **Regrade the loop-efficiency overlap to major** | G42-01: the matching `MajLoop.acc_poly` makes this an undisclosed re-proof of an already public lemma, beyond a predicate-name resemblance. The scanner generalization, fixed-test fiber inequality and chain-bound reuse remain notes. |
| SY-F07 | Agree: note | Canonical seals pass on the touched proof code; the seal-B and inherited Uniform failures are correctly attributed. |
| SY-F08 | Agree: note | The inline Mathlib lookup rewrites are expressly permitted. No new DL-47-shaped theorem was identified. The differing rewrite counts use different counting conventions. |
| SY-F09 | **Regrade step-comment omission to minor** | G42-03. The linter warning remains a note. |
| SY-F10 | Agree: note | Both hosts have public generic same-machine correctness/time/head contracts and draft promotion requests, as SY-4 permits. Promotion remains a maintainer decision. |
| SY-F11 | Agree: note | Uniformity is proved for both actual simulator constructions; the frozen statement need not be strengthened. |
| SY-F12 | Agree: accepted size exception | 1,179 ≤ 1,200; no size or width excess elsewhere. |

DL-49, DL-51 and DL-52 correctly identify their declarations and required cleanup. The newer rulings supersede the pack's stale “still open” language. G42-01 is outside those rows and keeps the gate open. No concrete #324/#327 name interaction was identified.

## Notation

`n`: security parameter; `S(n)`: polynomial circuit-size bound; `δ(n)`: negligible bad-seed bound; `μ(n)`: the single negligible B1 reduction bound for a fixed distinguisher.

## ===== briefs/pass-shelat-ch5-8/gates/42-sc-yao/pr-description-r2.md (this pack) =====

This is the landing PR of the Pass–shelat fill `sc-yao` (`PassShelatChapter5-8Plan.md`, prong B). It proves the two frozen Yao targets in `SecureComputation/Yao.lean`, which are Yao's garbled-circuit protocol [PS10, Protocol 162.6] in the bit-transfer (OT) hybrid model:
- `yaoHybrid_polyTime`: the hybrid protocol is polynomial time;
- `yaoHybrid_simulators`: the honest-but-curious simulators for Alice and Bob [PS10, Theorem 163.7].

`yaoHybrid_hbcSecure` follows from the two targets. The real protocol, `yaoProtocol_hbcSecure`, follows by composition with sc-compose's `HybridProtocol.hbcSecure_compose` (#324, merged). **On the merged tip it uses only the standard axioms.**

**Head:** `355a0288d56290e8c984228cbc1824187029e456`. **Base:** `cryptography/pass-shelat-ch2-4`, from the tip `f9fda8fe`. Since then the branch has gained #327 and #324 (`201bf57a`) and records only. Neither touches this PR's files, and the merge is clean.

## Changes (70 files against `f9fda8fe`)
- `Yao.lean`: only the six approved regions change, plus LE-title's title line. The file has 1195 lines, within the SY-2 waiver of 1,200.
- `Circuits/Uniform.lean`: seven SY-3 encoding readers, each a formula docstring with an `rfl`/`Iff.rfl` proof.
- The hub `Yao/HybridProof.lean` and 67 helpers under `Yao/HybridProof/`. Every line is at most 100 characters.
- `DAGCircuit.lean` is unchanged against the tip.

## Commits (15, all SSH-signed)
- The worker's 8 commits (Codex delivery, exchange `47c38c47`), rebased onto the tip with authorship kept.
- **Review landing edits:**
  - LE-bullet `13690d2e`;
  - LE-reuse `81d526d8` (SY-F05);
  - LE-title `bd7832d7`;
  - LE-doc `e9b03c43` (SY-F04, docstring-only).
- **Gate 42 round-1 landing edits:**
  - **LE-reuse-2** `26f0b77b` (G42-01): `RunWithHost.acc_poly` now derives from the public `StateLoop.MajLoop.acc_poly` through the two published readers. Proof-only; the docstring discloses the reuse.
  - **LE-refs** `3e99eb80` (G42-02): full `[AB09]` and `[BMR90]` bibliography entries.
  - **LE-steps** `355a0288` (G42-03): step comments in the six long proofs. Comment-only.

## Checks
- **Integration on the records tip.** Merge M of the tip with `e9b03c43`:
  - **772/772** modules rc 0, with 0 `error:`/`error(`, through root `TCSlib` and both `Checks`;
  - state check 1410/1410;
  - admissions **229 → 227**.
- **Gate 42 landing edits.** M′, M with `355a0288`: 20 modules rebuilt, 20/20 rc 0; state OK; `acc_poly`'s new body elaborates.
- **Axioms**, standard three only on M and M′:
  - `yaoProtocol_hbcSecure`, with 0 `sorryAx` users in its closure;
  - `yaoHybrid_hbcSecure`, `yaoHybrid_polyTime`, `yaoHybrid_simulators` and `yaoSeed_good_whp`;
  - `hbcSecure_compose` and all ten `otProtocol_*`;
  - `RunWithHost.acc_poly`.
- **Rule 10:**
  - `Yao.lean` seal A has 0 errors. Seal B has 24 errors in 9 declarations, all `PolyExpr.eval` conversions or cascades; this matches the review byte for byte.
  - `Uniform.lean`'s 4 errors are inherited from the tip.
  - Helpers: canonical coe-A seals pass on all 68.
  - `RunWithHost` after LE-reuse-2: coe and strict, A and B, all have 0 errors.
  - Paired controls are ALL_OK; the explicit-unfold scan finds 0 foreign unfolds.
- **Lint:** no new FAIL.

## Findings
- **Review r1** (ACCEPT WITH LANDING EDITS), with Seyoon's rulings:
  - SY-F01 is confirmed.
  - SY-F02 is ledger debt, DL-51.
  - SY-F03 is ledger debt, DL-49 extended.
  - SY-F05's remaining pair is ledger debt, DL-52, re-pointed after this merges.
- **Gate 42 round 1** (Codex, at `e9b03c43`): **HOLD**, with 0 blockers, 1 major and 2 minors. It found no mathematical gap. G42-01 to G42-03 are resolved by the three landing edits above (`briefs/pass-shelat-ch5-8/gates/42-sc-yao/resolutions-r1.md`).
- **Gate 42 round 2** at this head: being staged.

The evidence is in `briefs/pass-shelat-ch5-8/fills/sc-yao/final-r1/`: `review.md`, `review-evidence.zip`, `post-merge-addendum.md`, `rulings.md` and `integration-tip/`. Seyoon merges.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== briefs/pass-shelat-ch5-8/fills/sc-yao/final-r1/integration-tip/README.md (records, at 2da7e0f3cd65ec93ed71813b7828c3b66ba18942) =====

# sc-yao (#341) · integration build on the records tip

**Result for M: clean.** The landing head `e9b03c43` merged into the current records tip builds with 0 errors in both
forms through root `TCSlib` and both `Checks`. The whole-order state check passes. `yaoProtocol_hbcSecure` now uses only
the standard three axioms. Sorry warnings go from 229 at the tip to 227. The Yao seals are byte-identical to Phase 2's.

**Result for M' (Gate 42 landing edits, head `355a0288`): clean.**
- The 20 affected modules rebuild with rc 0 and 0 errors in both forms; the state check passes.
- `RunWithHost.acc_poly`'s new body elaborates, so no fallback body was needed. Its axioms are standard.
- All four RunWithHost seals give 0 errors.

**`dl-oleans-2`** was restored to snapshot `457ba704…`: SNAPSHOT EQUAL; extra 0, changed 0, missing 0.

The records branch gained 10 records-only commits during the job (`f22e0f67` → `c5eb7cf4`, and origin `f6f295a6`).
`TCSlib`, `TCSlib.lean`, `audits`, `scripts` and the lake files are unchanged across them, so M's code is still "current
tip + #341".

Date: 2026-11-16 UTC. Working directory: `$SP/dl-review/sc-yao-r1/int-tip/`, where `$SP` is this session's scratchpad.
All of it is in `integration-tip-evidence.zip` under `int-tip/`: SHA-256
`4d24501bca1d67a8cf8905448acb77b161a61a45e8d38f72f14dea2fca95d6d8`, 989 entries. `SHA256SUMS` lists every entry, then
the zip itself. Verified from a fresh extract: all 989 entries OK, with an exact path set.

## Inputs
- **Records tip** `T` = `f22e0f6798815b9263893e61928b4f16452f74ee`. Its `TCSlib`, `TCSlib.lean`, `audits`, `scripts`
  and lake files are the same git objects as in `201bf57a` (#324 merged) and in the int-x cross-built tree `199ea4c6`
  (`merge/merge-facts.txt`). `7d532e20` (#327) and `201bf57a` are ancestors of `T`.
- **#341 landing head** `H` = `e9b03c437aca251846430ff23b40ee5ff3d3347a`, built and reviewed in Phase 2 on `f9fda8fe`.
  `merge-base(T, H)` = `f9fda8fe`.
- **Olean tree** `$SP/dl-oleans-2` only. The other job's `$SP/dl-oleans` was not touched.

## Scratch merge M
- `git merge --no-ff --no-gpg-sign` of `H` into `T`, on the local branch `int/sc-yao-tip`, in a new sparse worktree
  (`$SP/wt-int-sc-yao-tip`; non-cone `/*`, without `briefs/`, `dataset/`, `blueprint/` and `dep_graph.json`).
  Author and committer dates are fixed at 2026-11-16T00:00:00Z. Nothing was pushed.
- **M** = `e327a5f284c043493e1b405b282e9abc5e002b61`, tree `741bafe2ce706adbf697ab893bf4bc28e7eb1d7d`, parents `T`, `H`.
  `git merge-tree --write-tree T H` gives the same tree, with rc 0.
- `git diff --raw --no-abbrev 201bf57a M -- TCSlib TCSlib.lean audits` is byte-identical to the same diff for
  `f9fda8fe e9b03c43`: 70 paths (68 added, 2 modified), with the same modes and old and new blobs. Over the whole tree, M
  differs from `T` in exactly these 70 paths (`merge/`).

## Build (step 4)
- **Method:** Phase 2's, with unmodified copies of its tools (`tools/`). `downorder.py` against the snapshot base
  `eff2dcd0` gives changed 250, downstream 772 and order 1410. `stateplan.py init` over the snapshot keys 1199 modules,
  and `state/state-init.json` is byte-equal to Phase 2's. `stateplan.py plan` at M gives 772 to build (561 snapshot
  modules with a changed closure key plus 211 new) and 638 to reuse. The queue equals `down.txt` and includes root
  `TCSlib`, `audits/pass-shelat/Checks` and `audits/garg-ch1-3/Checks`.
- **Backup:** the 561 snapshot oleans were hard-linked into `$SP/dl-sctip-backup`; all 561 hashes were checked against
  the snapshot. The 211 new modules are listed in `tree/new-oleans.txt`.
- **Mathlib overlay:** `mloverlay.sh` (3346 symlinks) and NthRootLemmas via `mathlibextra.sh`. Mathlib is `029db123`;
  the olean is `c0a9cff0…`, as in Phase 2 and int-x. It is the only one of the 377 Mathlib roots missing from the shared
  build.
- **Runner:** `scripts/lean_check_tree.sh` (byte-equal to the repository's) through `tools/runner.py`, one Lean process,
  with `TCSLIB_OLEANS=$SP/dl-oleans-2`. No lake command and no cache get were used.
- **Result:** 772/772 rc 0. `error:` 0, `error(` 0, combined 0, and no log contains the substring "error"
  (`build-m/permod.out`, `per-module.tsv`). Every log hash equals its record.
  - Runtime: 6721 s of module time, from 17:03:09 to 18:55:11 UTC. Peak RSS was 4.30 GB.
  - Disk: the lowest free space seen was 1538 MB (`build-m/df.log`). At about 17:46 another job took about 770 MB.
  - Sorry warnings: 89. This is X1's 91 minus `Yao.lean`'s 2.
  - sc-yao's 70 modules all give rc 0, 0 errors and 0 `sorry`. The only warning is in `BobIO`: line 211,
    an unnecessary `simpa`, as in Phase 2.
  - `ComposeSecurity` (#324) and `SequentialZK` (#327) both give 0 `sorry`.
- **References** (`refunion2.py` against Phase 2's `build-head` and int-x's `records-final`): all 772 oleans are
  byte-identical, in both source and olean, to at least one reference.
  - Two modules have a same-source reference with a different olean: `YaoReal` and the hub `SecureComputation`. In both
    cases that reference is int-x's X1, which does not contain sc-yao. Both are SAME as Phase 2. This is expected, since
    their import closures differ from X1's.
- **Closure keys against Phase 2:** 1327 of the 1356 common modules have equal keys. These include `Yao`,
  `Yao/HybridProof`, all 68 helpers, `Uniform` and `audits/garg-ch1-3/Checks`. Only the 29 #327/#324-affected modules
  differ: `YaoReal`, `ComposeSecurity`, the hub, the ZK/Composability modules, root `TCSlib` and
  `audits/pass-shelat/Checks` (`checks/closure-keys-vs-phase2.txt`).
- **State check:** `stateplan.py update` took all 772 modules. `stateplan.py check` at M over the 1410-module order gives
  1410/1410 OK, RESULT OK (`build-m/statecheck.txt`).

## Axioms (step 5)
The probes were `AxiomsLand` (Phase 2's, byte-identical) and `AxiomsTipExtra`, which covers every `otProtocol_*` result
plus `#admitted` traces and uses AxiomsLand's elaborator verbatim. Both ran through `runner_full.py` (rc 0, 0 errors).
Summaries are in `axioms-summary-*.txt`; the diff against Phase 2 is in `axioms-vs-phase2.diff`.

| Constant (`TCSlib.Cryptography.SecureComputation.`…) | Axioms on M | Phase 2 |
|---|---|---|
| `yaoProtocol_hbcSecure` | propext, Classical.choice, Quot.sound | + sorryAx (through `hbcSecure_compose`) |
| `yaoHybrid_hbcSecure` | propext, Classical.choice, Quot.sound | same |
| `yaoHybrid_polyTime` | propext, Classical.choice, Quot.sound | same |
| `yaoHybrid_simulators` | propext, Classical.choice, Quot.sound | same |
| `yaoSeed_good_whp` | propext, Classical.choice, Quot.sound | same |
| `HybridProtocol.hbcSecure_compose` | propext, Classical.choice, Quot.sound | + sorryAx |
| `otProtocol_P`, `_V`, `_rounds`, `_verifierFirst`, `_isOT`, `_outV`, `_outP`, `_simulators`, `_polyTime`, `_hbcSecure` | propext, Classical.choice, Quot.sound | `_polyTime`, `_simulators` same (others not probed) |

- **`#admitted`:** no closure has a direct `sorryAx` user.
  - `yaoProtocol_hbcSecure` has 21453 constants (20865 in Phase 2, which had 1 admitted constant,
    `hbcSecure_compose`).
  - `hbcSecure_compose` has 17721, the same as int-x X1.
  - `yaoHybrid_polyTime` has 9168, `yaoHybrid_simulators` 20202, `yaoHybrid_hbcSecure` 20475 and `yaoSeed_good_whp`
    17757, all as in Phase 2.
  - The `otProtocol_*` results have 16652, 7298 and 16742 (`_simulators`, `_polyTime`, `_hbcSecure`).
- **Owners census:** 1492 stored constants, 0 nonstandard, 27 simp lemmas, 11 instances. The 1492 `AX` rows and the
  `#check @…FakeSimulator.Data.make` output are identical to Phase 2's. The rest of the AxiomsLand log differs from
  Phase 2's only in the two `sorryAx` lines above.

## Admissions (step 6)
The int-x method: `tipcensus.py`, with each module's `declaration uses 'sorry'` count taken from rc-0 records with the
module's source. The record sets are M's build and int-x's `records-final` (`admissions/`).
- **Tip** (`201bf57a`, whose Lean is `T`'s): 229. Per module, this is identical to int-x's X1 census.
- **M:** 227 over 1410 modules with a record. The only change is `SecureComputation/Yao` 2 → 0. The 68 new modules all
  have 0, and no module was removed.
- The same 34 modules outside root `TCSlib`'s closure have no record at either revision. There are no disagreeing
  records.

## Rule 10 supplement: Yao seals (step 7)
- **Method:** Phase 2's `CollectLand` collector was rerun on M with `-DmaxErrors=0`. Its log is byte-identical to
  Phase 2's (CAT-COUNT 3991, one projection-coercion instance, `FinDist.instCoeFunForallReal`).
- **Generation:** `mkseals_sy.py` with the archived Gate 06/10 harness, coe variant (`SEAL_COE_FILE`) and
  `SEAL_CHUNK=2000`. A is the default; B uses `SEAL_EVAL=1`.
  - This gives 3046 requests for A and 3047 for B. Both probe files are byte-identical to Phase 2's run probes, and
    their records differ only in `rev` and `probe_module`.
- **Runs:** `runner_full.py` (`lean -DmaxErrors=0`, no `-o`); summaries from `sealsum.py` with Phase 2's
  `touched-head.json`, since `Yao.lean` has the same blob `47d4c268` at `H` and at M.

| Seal | Requests | rc | `error:` | `error(` | Declarations | Phase 2 |
|---|---|---|---|---|---|---|
| coe A | 3046 | 0 | 0 | 0 | none | 0 |
| coe B | 3047 | 1 | 24 | 0 | 9: `yaoCoins_eval`, `yaoHybrid`, `yaoHybrid_answersB_getD`, `yaoHybrid_callA`, `yaoHybrid_callB`, `yaoHybrid_hbcSecure`, `yaoHybrid_polyTime`, `yaoHybrid_simulators`, `yaoSeed_good_whp` | 24 in the same 9 |

- Install and EOF records are present in both logs. After the probe directory is renamed (`ScYaoSeal_coe` →
  `ScYaoTipSeal_coe`), both logs are byte-identical to Phase 2's, so the error positions and messages are identical
  (`seal-compare-phase2.txt`).
- There is no difference to explain. `Yao.lean`'s entire import closure is unchanged by #327 and #324: `Yao.lean` does
  not import `ComposeSecurity`, and only `YaoReal` does. Phase 2's attribution (`PolyExpr.eval` conversions or cascades)
  therefore carries over unchanged.

## Space (step 2)
Phase 2's `seal-runs`, `seals-coe`, `seals-strict`, `probe-sources-run`, `control-runs`, `controls-coe` and
`controls-strict` held 437 files, about 400 MB. Every one is in the committed `review-evidence.zip` (`d3f7c3da…`): the
same path under `phase2/`, the same SHA-256 in the zip entry and the same SHA-256 in `evidence-SHA256SUMS`. There were
no symlinks or special files. The directories were then deleted (`space/zipcover.txt`, `space/deleted.txt`).

## M' — Gate 42 landing edits (coordinator extension)
- **Head:** `355a0288d56290e8c984228cbc1824187029e456`, three commits on `e9b03c43`:
  - `26f0b77b` LE-reuse-2;
  - `3e99eb80` LE-refs;
  - `355a0288` LE-steps.

  Each carries an SSH signature header. The signatures are not verifiable here, because no `allowedSignersFile` is
  configured. In total, 9 files change, with 69 insertions and 3 deletions, and there are no import changes.
- **Scratch merge:** `git merge --no-ff --no-gpg-sign` of `355a0288` into `T`, on the local branch `int/sc-yao-tip-le`, in
  a second sparse worktree with the same dates.
  - **M'** = `061ad60cdc485e6248eeadfc2de165a227f7cd99`, tree `84c5381ba7188069f296f899efff9104f9b9bbe0`.
    `merge-tree` gives the same tree.
  - `git diff --raw 201bf57a M'` over the Lean paths equals `git diff --raw f9fda8fe 355a0288` (70 paths).
  - `git diff --raw M M'` over the whole tree equals `git diff --raw e9b03c43 355a0288` (9 paths)
    (`mprime/merge/merge-facts.txt`).
- **Build:** done on top of M's built state; nothing was restored in between.
  - The order at M' is byte-equal to M's (1410 modules). `stateplan.py plan` against M's updated state gives 20 to
    build and 1390 to reuse. The 20 are the 9 edited helpers and their downstream: `AliceProgram`, `DescriptionDecoder`,
    `GarbledRun`, `BobProgram`, `FakeSimulator`, `SelectedStepSecurity`, `GateHybridSecurity`, the hub
    `Yao/HybridProof`, `Yao`, `YaoReal`, the `SecureComputation` hub and root `TCSlib`. `audits/*/Checks` keep their
    keys.
  - All 20 are in M's queue (4 in the snapshot backup and 16 in `new-oleans.txt`), so the restore covers them.
  - **Result:** 20/20 rc 0. `error:` 0, `error(` 0 and substring 0. There are 0 `sorry` and 1 warning, the
    unnecessary `simpa` in `BobIO`, now at line 218 (moved from line 211), as expected.
  - 159 s of module time, 19:05:49–19:08:28 UTC, peak RSS 4.31 GB. `Yao.lean` is 1195 lines.
  - **State check:** `update` took all 20, and `check` at M' gives 1410/1410 OK, RESULT OK
    (`mprime/build/statecheck.txt`).
  - **Admissions:** `tipcensus.py` at M' gives 227, the same as M in every module.
- **Axioms** (`AxiomsLand` unmodified, plus `AxiomsLE`; rc 0, 0 errors):
  - `yaoProtocol_hbcSecure`, `yaoHybrid_hbcSecure`, `yaoHybrid_polyTime`, `yaoHybrid_simulators` and `yaoSeed_good_whp`
    use propext, Classical.choice and Quot.sound. No closure has a direct `sorryAx` user.
  - Closures: `yaoHybrid_polyTime` 9172, `yaoHybrid_hbcSecure` 20479 and `yaoProtocol_hbcSecure` 21457, each 4 more
    than at M (the reused `MajLoop.acc_poly` chain). `yaoHybrid_simulators` (20202) and `yaoSeed_good_whp` (17757) are
    unchanged.
  - `YaoHybridProof.RunWithHost.acc_poly` uses propext, Classical.choice and Quot.sound, and its closure (4610) has no
    `sorryAx` user. `Complexity.StateLoop.MajLoop.acc_poly` uses the same three.
  - The `#check` output of `acc_poly`, `MajLoop.acc_poly`, `RunWithHost.acc_eq` and `MajLoop.acc_eq` confirms that the
    statement is unchanged and that the two readers state the same predicate.
  - The owners census is unchanged: 1492 stored constants, all standard, with the same `AX` rows as M
    (`mprime/axioms-vs-M.diff`).
- **Seals on `Yao/HybridProof/RunWithHost.lean`:** `CollectLand` was rerun at M' (CAT-COUNT 3991; coe names unchanged).
  Seals were made with `mkseals_sy.py` as above and run with `-DmaxErrors=0`.

| Variant | Requests | rc | `error:` | `error(` | Install / EOF |
|---|---|---|---|---|---|
| coe A (canonical) | 844 | 0 | 0 | 0 | yes / yes |
| strict A | 844 | 0 | 0 | 0 | yes / yes |
| coe B | 845 | 0 | 0 | 0 | yes / yes |
| strict B | 845 | 0 | 0 | 0 | yes / yes |

  - Phase 2's coe A on this file at `e9b03c43` also had 844 requests and 0 errors.
  - The coe and strict probes are byte-identical, because no projection-coercion instance is in this file's closure.
  - `Complexity.StateLoop.MajLoop.acc` is a sealed row in all four variants. The new body reaches it only through the
    readers `acc_eq` and `MajLoop.acc_eq`, and it passes under the seal. `RunWithHost.acc` is the file's own definition,
    so it is outside the sealed import closure by design.
- **Fallbacks:** neither of the two fallback bodies in `26f0b77b`'s message was tried, because the committed body
  elaborates. Nothing was committed.

## Restore (step 8)
`tools/restore-tree.sh` is Phase 2's `restore-tree.sh` with only the backup directory, the evidence directory and the
order path changed (`tools/restore-tree.phase2.sh`). It was run after M' (`restore/restore-log.txt`).
- **Backup:** hash failures 0. Of the 561 backed-up oleans, 40 were restored from the backup. The other 521 rebuilt
  oleans were already byte-identical to the snapshot.
- **Deletions:** the 211 new oleans were deleted, each hash logged. The Mathlib overlay was deleted: 3346 symlinks and
  NthRootLemmas.
- **Snapshot:** `tree/snapshot-post.txt` has 1230 files, 0 empty directories and SHA-256
  `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`, byte-equal to `tree/snapshot-pre.txt`
  (**SNAPSHOT EQUAL**). `restoreplan.py` reports extra 0, changed 0 and missing 0 (`restore/plan/`).
- **Independent recheck:** a fresh snapshot (`restore/snapshot-recheck.txt`) is equal to the pre-snapshot, and
  `restoreplan.py` again reports extra 0, changed 0 and missing 0 (`restore/verify-plan/`). There are no symlinks, no
  `Mathlib/` and no empty directories (`restore/restore-verify.out`).
- The script's own `tee restore/restore.out` could not open its file, because `restore/` is created by the script. This
  is the same quirk int-x recorded; the lines are in `restore-log.txt` and `restore-verify.out`.
- **Cleanup** (`cleanup.txt`): the backup, the probe directories, both scratch worktrees and the temporary extracts were
  removed. The local branches `int/sc-yao-tip` (M) and `int/sc-yao-tip-le` (M') are kept; neither has an upstream, and
  nothing was pushed. No commit was made on `/home/user/tcslib`.
  - A first combined cleanup command was refused by the built-in safety check on variable-expanded `rm` targets, and
    nothing in it ran. The removals were then made with literal paths, the form the check names as safe.

## Layout of the zip (`int-tip/`)
- `merge/`, `mprime/merge/`: merge facts and raw diffs.
- `order-m/`, `plan-m/`, `state/`, `tree/`: inputs, state and snapshots.
- `build-mathlib-extra/`: the Mathlib overlay and NthRootLemmas.
- `build-m/`: per-module records, logs, `permod`, the state check, `refunion` and `df.log`.
- `checks/`: closure keys against Phase 2.
- `probe-src/`, `probe-runs/`, `axioms-*`: axiom probes.
- `admissions/`: the sorry census.
- `seals-coe/`, `seal-runs/`, `seal-sum-*`, `seal-compare-phase2.txt`: Yao seals.
- `mprime/`: M' order, plan, state, build, probes, census and RunWithHost seals.
- `restore/`, `space/`, `cleanup.txt`: restore, space and cleanup records.
- `tools/` with `run-build-m.sh`, `tip-probes.sh`, `mprime/*.sh` and `diskwatch.sh`: every script that was run.
  - New scripts: `zipcover.py`, `axsum.py`, `mkevidence.py`, and the probes `AxiomsTipExtra.lean` and `AxiomsLE.lean`.
  - Everything else is an unmodified copy of Phase 2's tools.

## ===== verification-r2.zip:records/decision-log-sc-yao.md (this pack) =====

Extract of PassShelatChapter5-8Plan.md at the records pin 2da7e0f3cd65ec93ed71813b7828c3b66ba18942: lines 177-180 (the decision-log heading and table header) and 816-829 (the decision-log rows from the sc-yao final delivery to the start of this staging), byte for byte.

## Decision log

| Date | Decision | Status |
|---|---|---|
| 2026-11-16 | **sc-yao final delivered** (exchange `47c38c479`): REPORT claims `yaoHybrid_polyTime` proved (standard axioms) and `yaoHybrid_simulators` proved modulo exactly sc-garble's frozen `yaoSeed_good_whp` and `sliceMultiMessageSecure_of_prfOut` (admitted at the issue base `6ce4658d`; sc-garble has since merged as #323); 8 unsigned commits, local tip `6e7ef601`; one hub `Yao.HybridProof` importing 67 helpers (14,306 lines, max 577 per file); `Yao.lean` 1,152 lines (1,180 with sc-garble's lines, under the SY-2 cap of 1,200); the 8 SY-3 readers; admissions 32 → 30. Maintainer review and landing preparation onto the tip started (drop the duplicate `isFaninTwo_iff`, now on the tip; merge the main-results bullets); Lean phase when a tree frees. With sc-yao landed, PS10 chapters 5–8 are formalized modulo sc-compose (#324). | Under review |
| 2026-11-16 | **sc-yao review, phase 1 and landing prep: provisional ACCEPT WITH LANDING EDITS** (`fills/sc-yao/final-r1/review.md`, interim; phase-1 evidence zip `9cad72f0`): manifests exact (7597/7597, 7515/7515); `git am` reproduces all 8 commits (`6e7ef601`); `Yao.lean` outside the six approved regions byte-identical to the base (controls OK); `DAGCircuit.lean`/`Uniform.lean` carry only the 8 SY-3 readers; 68 hub files, 14,306 lines, max 577, width ≤ 100; delivered seals: helpers 0 errors, Yao seal A 0, seal B 24 vs 15 at base (the 9 new are `PolyExpr.eval` conversions, notation per the 2026-11-14 ruling); unfold scan 0 foreign; admissions on the tip 23 → 21, none left in `Yao.lean`. Landing branch `land/pass-shelat-sc-yao` (local) at `bd7832d7` on the tip `f9fda8fe`: worker commits cherry-picked (authorship kept; `isFaninTwo_iff` absorbed, identical to #323's; main-results bullets kept both), plus signed LE-bullet (`13690d2e`, "proved modulo sc-garble" → "proved"), LE-reuse (`81d526d8`, two `CoinSeedRelabel` lemmas via the public `GarblingProbability.assignmentFold_small`, proof only), LE-title (`bd7832d7`, drops "(statement phase)"); `Yao.lean` 1,179 lines (cap 1,200). Findings: SY-F01 minor (four helper imports outside the issued order, approved by Seyoon only inside the worker session: **needs Seyoon's confirmation**); SY-F02/SY-F03 minor undisclosed restatements (`statClose_of_eq_off` vs public `statClose_of_uprob_ne`; `encodeMsgs_eq_encWords`, DL-49 class): ledger + promotion proposed; SY-F04 minor (formula docstrings missing on many helpers: LE-doc before the gate); SY-F05 (one SY-5 copy pair open until #324 lands); SY-F06..12 info. Phase 2 (Lean) waits for a tree. | Phase 2 pending |
| 2026-11-16 | **Cross-build tip × #327 × #324: PASS** (`dl-oleans-2`; evidence `maintainer/int-x-327-324-2026-11-16/int-x-327-324-333-evidence.zip`, `d8a4839e`). Tip `8c42b40d` (with #332, #333; code identical to C2). A = tip × #327 `d9884a4e` (clean); X1 = A × #324 `ffde82d6`, tree `199ea4c6` (clean; reverse order gives the same tree; diff vs tip = 57 files, blob-equal to the PR heads). Closure 1342 modules incl. root and both Checks; 704 rebuilt, 704/704 rc 0, 0 `error:`/`error(`; every rebuilt olean and log byte-equal to a reference record; state and whole-tree checks OK. Sorry totals 237 → 229 (SequentialZK 5 → 0, ComposeSecurity 3 → 0). Axioms at X1: the five `seqRep` targets and `hbcSecure_compose` standard, no `sorryAx` in their closures; `yaoProtocol_hbcSecure` reaches `sorryAx` only via the two Yao admissions (sc-yao, under review). No name clash among #332/#333/#327/#324. The 09:00 ENOSPC stop (another job's export) handled: 44 suspect records set aside in `spurious-enospc/`, rebuilt, all equal to references. `dl-oleans-2` restored (SNAPSHOT EQUAL). **#327 then #324 are clear to merge.** | #327, #324 clear to merge |
| 2026-11-16 | **#327 and #324 merged** (Seyoon): #327 as `7d532e20`, then #324 as `201bf57a`. The merged Lean equals the cross-built tree X1 `199ea4c6` byte for byte (`git diff` over `TCSlib/`, root, lakefile, manifest and toolchain is empty), so the tip's admissions are **229** (SequentialZK and ComposeSecurity at 0). The merges touch only `SequentialZK/`, `ComposeSecurity/` and one reader (`StatZK_iff`) in `ZeroKnowledge/Defs`: none of #331's, #338's, #339's or #340's files, and none of their 388 new declaration names occur among those PRs' added names. Gate 40 r2 and Gate 43 dispatch prompts refreshed (merge-condition sentence only; pins unchanged). Integration builds of #331 and of #338 × #339 on `201bf57a` stay maintainer merge conditions (both olean trees are busy with sc-yao phase 2 and T4). | Gate 40 r2, Gate 43 ready to dispatch |
| 2026-11-16 | **sc-yao review r1 final: ACCEPT WITH LANDING EDITS** (`fills/sc-yao/final-r1/review.md`; evidence `review-evidence.zip` `d3f7c3da`, 1511 entries, `evidence-SHA256SUMS`; `landing/PROVENANCE.txt`). Landing head `e9b03c43` (12 signed commits on `f9fda8fe`: the worker's 8, LE-bullet, LE-reuse, LE-title, LE-doc). Phase 2 on `dl-oleans-2`: 718/718 rc 0, 0 errors, state 1356/1356; `yaoHybrid_polyTime`, `yaoHybrid_simulators`, `yaoHybrid_hbcSecure`, `yaoSeed_good_whp` standard; `yaoProtocol_hbcSecure` then reached `sorryAx` only via #324's `hbcSecure_compose`. Rule 10: Yao A 0, B 24 (9 new, all `PolyExpr.eval` conversions), `Uniform` 4 inherited, helpers coe-A 68/68, controls ALL_OK. Lint: no new FAIL. Tree restored (SNAPSHOT EQUAL). Findings SY-F01 (confirm 4 imports), SY-F02, SY-F03 (ledger recommended) pending Seyoon; SY-F04 fixed. **Post-merge addendum** (`post-merge-addendum.md`): merge with `201bf57a` clean, no file overlap, no name clash; SY-F03 extended (sc-yao's `encodeMsgs_eq_encWords` now copies #327's public `SequentialZK.encodeMsgs_eq_encWords`, itself unledgered DL-49 class); SY-F05's `OTAnswerWords` pair goes to the post-merge cleanup. Next: push the landing branch, draft PR, integration build on the new tip (`dl-oleans-2`), Gate 42 (Codex). | sc-yao ACCEPT WITH LE; PR + Gate 42 next |
| 2026-11-16 | **Draft PR #341 opened** (sc-yao landing, head `e9b03c43`, branch `land/pass-shelat-sc-yao` pushed). Started: the integration build of #341 × the tip `f22e0f67` on `dl-oleans-2` (merge condition; `yaoProtocol_hbcSecure` expected standard now that #324 is merged), and Gate 42 staging (Codex; records pin `f22e0f67`). DW-5/DW-4 cleanup waits for a free tree. | #341 Gate 42 staging |
| 2026-11-16 | **Rulings (Seyoon) on sc-yao (#341):** SY-F01 confirmed (the four helper imports); SY-F02 ledger then promote (DL-51; `statClose_of_uprob_ne` to `Asymptotic/Sampling` in the cleanup); SY-F03 ledger both (DL-49 extended with sc-yao's and #327's `encodeMsgs_eq_encWords`; one common copy in the cleanup). No change to #341. `fills/sc-yao/final-r1/rulings.md`. DW-4 now spans DL-38 to DL-51. Still to acknowledge: SY-F05's `OTAnswerWords` pair against #324's `HybridProtocol.length_answers*` (recommended ledger, re-point after #341 merges). | SY-F01–F03 ruled |
| 2026-11-16 | **Gate 42 staged** (Codex; sc-yao #341 at `e9b03c43`; records pin `f22e0f67`, rulings `67423db6`, wording correction `d6fe1ddd`, gate directory `895bc778`). Exchange commit `747b61e7` on `14e681e6`, pushed: 23 files under `outbox/gates/42-sc-yao-gate/` and nothing else; signed; SHA256SUMS verify. The records copy is `gates/42-sc-yao/` (pack, diff `f9fda8fe..e9b03c43` with 70 paths, sources with PS10 §6.2 pp. 154–164 extracted from the committed PDF, a 249-entry verification zip pointing at the committed review evidence). The pack raises for Codex: the DL-49 wording (now corrected); `[AB09]`/`[BMR90]` cited in `ChunkScanner`/`GarblingProgram` but missing from their `## References`; a fourth shared short name, `outV_eq`, in different namespaces; the review's scope check treating LE-title as approved. SY-F05's `OTAnswerWords` pair awaits Seyoon's acknowledgement. | Gate 42 ready to dispatch |
| 2026-11-16 | **Ruling SY-F05 remainder (Seyoon): ledger, then re-point after #341 merges.** Ledger row DL-52 (`OTAnswerWords.length_answersB`/`answersA_nil` against #324's `HybridProtocol.length_answersB/A`). This closes the last open sc-yao disposition; no change to #341. DW-4 now spans DL-38 to DL-52. | sc-yao dispositions complete |
| 2026-11-16 | **Gate 42 dispatched** (Seyoon; Codex) at #341 head `e9b03c43`, exchange `747b61e7`, records pin `f22e0f67`, with the rulings `67423db6`, the wording correction `d6fe1ddd` and the SY-F05 ruling `bf08dbfa` named in the prompt. Awaiting findings. The integration build of #341 on the new tip is still running (`dl-oleans-2`). | Gate 42 out |
| 2026-11-16 | **Gate 42 round 1: HOLD** (Codex; 0 blockers, 1 major, 2 minors; `gates/42-sc-yao/findings/gate42-sc-yao-findings.md` `e1076c1e`; `resolutions-r1.md`). No mathematical gap; the proofs, frozen files, landing edits, Rule 10, build and axioms are confirmed, and SY-F01–F05 are resolved or accepted under the rulings. Open items: **G42-01 major**, an undisclosed re-proof (`RunWithHost.acc_poly` = public `StateLoop.MajLoop.acc_poly`, no import needed), resolved by proof-only **LE-reuse-2**; **G42-02** missing `[AB09]`/`[BMR90]` bibliography entries, resolved by **LE-refs**; **G42-03** step comments in six long proofs, resolved by **LE-steps**. The landing edits are being written; the new head is then checked on the integration tree and goes to Gate 42 round 2. | Gate 42 HOLD → LE |
| 2026-11-16 | **Gate 42 landing edits written** on `land/pass-shelat-sc-yao` (local, not pushed), three signed commits on `e9b03c43`. **LE-reuse-2** `26f0b77b` (G42-01): `RunWithHost.acc_poly` is derived from `StateLoop.MajLoop.acc_poly` through the readers `acc_eq` and `MajLoop.acc_eq` (proof-only; the docstring discloses the reuse; two fallbacks are in the message). **LE-refs** `3e99eb80` (G42-02): full `[AB09]` and `[BMR90]` entries. **LE-steps** `355a0288` (G42-03): step comments in the six proofs. Checks without Lean: LE-refs and LE-steps are pure comment-line insertions (docstrip CODE-EQUAL; byte-level removal restores the parent); LE-reuse-2 touches only `acc_poly`; the `Yao.lean` frozen check passes (only LE-title's line, controls behave); `Yao.lean` has 1195 lines (≤ 1200, SY-2); all lines ≤ 100 characters. The head `355a0288` is passed to the running sc-yao integration job for an incremental check on `dl-oleans-2` before restore; then push, Gate 42 round 2. | G42 LE written; check pending |
| 2026-11-16 | **sc-yao integration on the records tip: PASS; Gate 42 landing edits checked: PASS** (`dl-oleans-2`; evidence `fills/sc-yao/final-r1/integration-tip/`, zip `4d24501b`, 989 entries). M = `f22e0f67` merged with `e9b03c43` (`e327a5f2`; diff against `201bf57a` equals #341's 70 paths): 772/772 rc 0, 0 `error:`/`error(`, root and both `Checks`; state 1410/1410. **`yaoProtocol_hbcSecure` uses only the standard axioms** (its closure has 0 `sorryAx` users), as do `yaoHybrid_*`, `yaoSeed_good_whp`, `hbcSecure_compose` and all ten `otProtocol_*`. Admissions 229 → 227. Yao seals coe A 0 and B 24 in the same 9 declarations, byte-identical to Phase 2. M′ = M merged with the landing-edit head `355a0288` (`061ad60c`): 20 rebuilt, 20/20 rc 0; state OK; admissions 227; `acc_poly`'s new body elaborates (no fallback); axioms standard; `RunWithHost` seals coe/strict A/B all 0 errors. `dl-oleans-2` restored (SNAPSHOT EQUAL). The Phase 2 raw directories (all inside the committed review zip) were deleted to free about 400 MB. `land/pass-shelat-sc-yao` pushed at `355a0288`. Next: Gate 42 round 2. | #341 integration PASS; G42 r2 next |
| 2026-11-16 | #341's description updated to head `355a0288` (Gate 42 r1 landing edits; integration PASS; `yaoProtocol_hbcSecure` standard). **Started:** Gate 42 round 2 staging (no tree), and **DW-5** (derand typed-view readers for `ModuleHost`/`IterateFindHost`, re-deriving E1 `computesFunInTime_find` and `polyTimeComputable_find` through them, targeting 0 of F-01's 20 seal failures) on the freed `dl-oleans-2`, branch `cleanup/dw5-derand-readers`. | G42 r2 staging; DW-5 running |

## ===== verification-r2.zip:checks/series-r2.txt (this pack) =====

records pin (round 2) 2da7e0f3cd65ec93ed71813b7828c3b66ba18942: Records: #341 description at 355a0288; Gate 42 r2 staging and DW-5 started
  descends from round 1's records pin f22e0f67: True; and from 67423db6 (SY-F01..F03 rulings): True; d6fe1ddd (DL-49 wording correction): True; bf08dbfa (SY-F05 ruling (DL-52)): True; 9fa48035 (round-1 findings and resolutions): True; ed0d2acc (integration evidence): True
  code paths (TCSlib, TCSlib.lean, audits, scripts, lake files) changed f22e0f67..2da7e0f3: 0 []; so the integration tip T = f22e0f67 has the pin's code
  code paths changed 201bf57a (#327, #324 merged)..2da7e0f3: 0
  commits f22e0f67..2da7e0f3: 25
  pin commit signature: gpgsig 1, ssh-ed25519 key SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc, namespace git, verified True

PR #341 (GitHub REST GET /repos/Shilun-Allan-Li/tcslib/pulls/341, 2026-11-16; the MCP pull_request_read of the same time gives the same body): state open, draft True, head land/pass-shelat-sc-yao 355a0288d56290e8c984228cbc1824187029e456, base cryptography/pass-shelat-ch2-4 (REST base.sha f22e0f6798815b9263893e61928b4f16452f74ee), changed_files 70, +15879/-67, commits 15, updated_at 2026-11-16T19:17:57Z
  REST head = 355a0288d56290e8c984228cbc1824187029e456: True; body sha256 8b969b835f961eb556042d34e01333925244ab756d26e77294b3e785bc451ec1 (4122 bytes); = pr-description-r2.md: True
  origin/land/pass-shelat-sc-yao = 355a0288d56290e8c984228cbc1824187029e456 (= head: True); head tree 3cf1047be5c1dff4c3f4f6cffa4c926b6f0d1de7

round-1 head e9b03c43 is an ancestor of the head (no rebase): True; commits e9b03c43..355a0288: 3 = the three landing edits True; first-parent chain, no merges: True
  LE-reuse-2 (G42-01) 26f0b77bd22a3e3366778eb40ce7ddc68b6263ea: parent e9b03c437aca251846430ff23b40ee5ff3d3347a; author Claude <noreply@anthropic.com> 2026-11-16T18:19:20+00:00; committer Claude <noreply@anthropic.com>; gpgsig 1 ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc ns=git verified=True; same key as the records pin: True; Co-Authored-By and Claude-Session trailers present: True, True
    subject: sc-yao landing edit LE-reuse-2: RunWithHost.acc_poly from StateLoop.MajLoop.acc_poly (G42-01)
    1 file changed, 8 insertions(+), 3 deletions(-)
  LE-refs (G42-02) 3e99eb80109a7d5310acd890612e32385d3f1abc: parent 26f0b77bd22a3e3366778eb40ce7ddc68b6263ea; author Claude <noreply@anthropic.com> 2026-11-16T18:20:09+00:00; committer Claude <noreply@anthropic.com>; gpgsig 1 ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc ns=git verified=True; same key as the records pin: True; Co-Authored-By and Claude-Session trailers present: True, True
    subject: sc-yao landing edit LE-refs: full AB09 and BMR90 reference entries (G42-02)
    2 files changed, 5 insertions(+)
  LE-steps (G42-03) 355a0288d56290e8c984228cbc1824187029e456: parent 3e99eb80109a7d5310acd890612e32385d3f1abc; author Claude <noreply@anthropic.com> 2026-11-16T18:24:09+00:00; committer Claude <noreply@anthropic.com>; gpgsig 1 ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc ns=git verified=True; same key as the records pin: True; Co-Authored-By and Claude-Session trailers present: True, True
    subject: sc-yao landing edit LE-steps: step comments in six long proofs (G42-03)
    6 files changed, 56 insertions(+)
  signature control: the head with one byte added to its committer line verifies: False (expected False)

merge base of the head with the records pin: f9fda8fe8d11fc68c233df2979a86d356ddfe1ab (= the PR base f9fda8fe, as in round 1: True)
pr.diff-r2.txt = git diff f9fda8fe..355a0288: 916426 bytes, sha256 e4dd363426fdf0e6dc1c01d1399502e302dae3ed94441f4064619ebd8d846567; 70 files changed, 15879 insertions(+), 67 deletions(-)
  = git diff 2da7e0f3...355a0288 (three-dot, GitHub's view) byte for byte: True
  paths 70 ({'M': 2, 'A': 68}); the same paths and statuses as round 1's pr.diff.txt (f9fda8fe..e9b03c43): True
  round 1's records pr.diff.txt = git diff f9fda8fe..e9b03c43: True
pr-r2.diff.txt = git diff e9b03c43..355a0288 (round 1 -> round 2): 21944 bytes, sha256 bdd6717d5f2c55577ef5d83f43a2216901c73fd01fb656f183491fefc944124a; 9 files changed, 69 insertions(+), 3 deletions(-); paths 9, all among the PR's 70: True
  = the concatenation of the three commits' diffs, path by path: True
  TCSlib/Cryptography/SecureComputation/Yao.lean: ['16', '0'] (added, deleted)
  TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean: ['7', '0'] (added, deleted)
  TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean: ['3', '0'] (added, deleted)
  TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean: ['13', '0'] (added, deleted)
  TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulatorFactory.lean: ['3', '0'] (added, deleted)
  TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean: ['2', '0'] (added, deleted)
  TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean: ['8', '3'] (added, deleted)
  TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SeedCoordinates.lean: ['8', '0'] (added, deleted)
  TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SelectedLaw.lean: ['9', '0'] (added, deleted)

## ===== verification-r2.zip:checks/le-r2.txt (this pack) =====

=== LE-reuse-2 26f0b77bd22a3e3366778eb40ce7ddc68b6263ea (G42-01; parent e9b03c43): 1 file(s); 1 file changed, 8 insertions(+), 3 deletions(-)
  Yao/HybridProof/RunWithHost.lean: hunks 2 ({'insert': 1, 'replace': 1}); imports byte-identical True; identical after stripping comments False
    declarations 9 -> 9, same names in the same order True; headers (keyword to the top-level `:=`) byte-identical for all True; declarations whose docstring-to-end span differs: ['acc_poly']
    the file outside acc_poly's span (docstring to the next blank line) byte-identical: True
    acc_poly header at parent and head: 'theorem acc_poly : PolyTimeComputable fun w => [acc w] ' | 'theorem acc_poly : PolyTimeComputable fun w => [acc w] '; equal True
    acc_poly docstring: 2 -> 3 lines; pure insertion True; inserted ['Reuses `StateLoop.MajLoop.acc_poly`.']; formula line kept: True ('`PolyTimeComputable fun w => [acc w]`. -/')
    old declaration (parent):
      | theorem acc_poly : PolyTimeComputable fun w => [acc w] :=
      |   polyTimeComputable_isNil.comp
      |     (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
    new declaration (head):
      | theorem acc_poly : PolyTimeComputable fun w => [acc w] := by
      |   have hacc : ∀ w, acc w = Complexity.StateLoop.MajLoop.acc w := fun w =>
      |     (acc_eq w).trans (Complexity.StateLoop.MajLoop.acc_eq w).symm
      |   have hfun : (fun w => [acc w]) = fun w => [Complexity.StateLoop.MajLoop.acc w] :=
      |     funext fun w => congrArg (fun b : Bool => [b]) (hacc w)
      |   rw [hfun]
      |   exact Complexity.StateLoop.MajLoop.acc_poly
    identifiers in the new proof: ['Bool', 'Complexity.StateLoop.MajLoop.acc', 'Complexity.StateLoop.MajLoop.acc_eq', 'Complexity.StateLoop.MajLoop.acc_poly', 'acc', 'acc_eq', 'b', 'congrArg', 'exact', 'fun', 'funext', 'hacc', 'have', 'hfun', 'rw', 'symm', 'trans', 'w']
    definition-reading tactics or terms in the new proof (unfold, delta, simp, dsimp, show, rfl, decide, change, native_decide, Eq.mpr, cast): []; the only rewrite is `rw [hfun]` with the local equation hfun
    the readers used: acc_eq (this file) and Complexity.StateLoop.MajLoop.acc_eq: True; MajLoop.acc_poly applied: True
    Codex's candidate body (`simpa only [acc_eq, Complexity.StateLoop.MajLoop.acc_eq] using Complexity.StateLoop.MajLoop.acc_poly`) is the committed body: False; it is "Fallback 1" in the commit message, which keeps it and a second fallback untried:
      > Gate 42 G42-01 (major): `RunWithHost.acc_poly` re-proved the public
      > `Complexity.StateLoop.MajLoop.acc_poly` (Complexity/Randomized/Build/StringLoops.lean:144)
      > for the same word predicate `decide (pairFstD (pairSndD w) = [])`. Proof only: the
      > statement, the formula line of the docstring and the imports are byte-identical. The body
      > now identifies the two acceptance tests pointwise through their published readers only
      > (`acc_eq` and `Complexity.StateLoop.MajLoop.acc_eq`, joined by `Eq.trans`, so neither
      > definition is unfolded), rewrites the function and applies `MajLoop.acc_poly`. The
      > docstring gains the disclosure "Reuses `StateLoop.MajLoop.acc_poly`.". No import change:
      > RunWithHost already reaches StringLoops through Complexity.Randomized.Repetition.
      > 
      > Not elaborated here (no Lean run); the integration check decides. Fallback bodies, each
      > keeping the same statement and readers, in order of preference:
      > 
      > Fallback 1 (Codex's candidate):
      >   theorem acc_poly : PolyTimeComputable fun w => [acc w] := by
      >     simpa only [acc_eq, Complexity.StateLoop.MajLoop.acc_eq] using
      >       Complexity.StateLoop.MajLoop.acc_poly
      > 
      > Fallback 2 (funext and rewrites through the readers, cast by Eq.mpr):
      >   theorem acc_poly : PolyTimeComputable fun w => [acc w] := by
      >     have hfun : (fun w => [acc w]) = fun w => [Complexity.StateLoop.MajLoop.acc w] := by
      >       funext w
      >       rw [acc_eq, Complexity.StateLoop.MajLoop.acc_eq]
      >     exact (congrArg PolyTimeComputable hfun).mpr Complexity.StateLoop.MajLoop.acc_poly
      > 
=== LE-refs 3e99eb80109a7d5310acd890612e32385d3f1abc (G42-02; parent 26f0b77b): 2 file(s); 2 files changed, 5 insertions(+)
  Yao/HybridProof/ChunkScanner.lean: hunks 1 ({'insert': 1}); imports byte-identical True; identical after stripping comments True
  Yao/HybridProof/GarblingProgram.lean: hunks 1 ({'insert': 1}); imports byte-identical True; identical after stripping comments True
  all hunks pure insertions: True; removing the inserted lines restores the parent byte for byte: True
  every inserted line inside the module docstring `/-! ... -/`: True
  Yao/HybridProof/ChunkScanner.lean inserted:
    + 
    + * [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
    +   Cambridge University Press, 2009, §6.2 (descriptions of uniform circuit families).
  Yao/HybridProof/GarblingProgram.lean inserted:
    + * [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*,
    +   STOC 1990, pp. 503–513 (point-and-permute row order of the garbled tables).
  LE-refs message, without the trailer lines:
    > Gate 42 G42-02 (minor): two module docstrings cited a tag without its bibliography entry.
    > - ChunkScanner.lean: the `## References` section used `[AB09, §6.2]` only in prose; it
    >   gains the full AB09 entry (Arora-Barak, Cambridge University Press, 2009, §6.2), in the
    >   format of the sibling DescriptionDecoder.lean and of CircuitComplexity/Adder.lean.
    > - GarblingProgram.lean: `tables_poly`'s docstring cites `[PS10, Protocol 162.6; BMR90]`
    >   but the references listed only PS10; it gains the full BMR90 entry (Beaver, Micali,
    >   Rogaway, "The round complexity of secure protocols", STOC 1990, pp. 503-513), in the
    >   format of the sibling RowFromCoins.lean and CoinRelabel.lean.
    > Docstrings only: stripping comments and doc comments gives identical code.
    > 
=== LE-steps 355a0288d56290e8c984228cbc1824187029e456 (G42-03; parent 3e99eb80): 6 file(s); 6 files changed, 56 insertions(+)
  Yao.lean: hunks 8 ({'insert': 8}); imports byte-identical True; identical after stripping comments True
  Yao/HybridProof/BobIO.lean: hunks 6 ({'insert': 6}); imports byte-identical True; identical after stripping comments True
  Yao/HybridProof/FakeProgram.lean: hunks 7 ({'insert': 7}); imports byte-identical True; identical after stripping comments True
  Yao/HybridProof/FakeSimulatorFactory.lean: hunks 3 ({'insert': 3}); imports byte-identical True; identical after stripping comments True
  Yao/HybridProof/SeedCoordinates.lean: hunks 4 ({'insert': 4}); imports byte-identical True; identical after stripping comments True
  Yao/HybridProof/SelectedLaw.lean: hunks 7 ({'insert': 7}); imports byte-identical True; identical after stripping comments True
  all hunks pure insertions: True; removing the inserted lines restores the parent byte for byte: True
  every inserted line is a `-- ` line comment: True; each comment at the indentation of the next code line: True
  Yao.lean `yaoHybrid_polyTime`: 8 step comments, numbered [1, 2, 3, 4, 5, 6, 7, 8] (consecutive from 1: True), head lines [865, 897, 904, 936, 943, 950, 964, 973]
  Yao/HybridProof/BobIO.lean `outputBit_poly`: 6 step comments, numbered [1, 2, 3, 4, 5, 6] (consecutive from 1: True), head lines [100, 114, 118, 128, 132, 143]
  Yao/HybridProof/FakeProgram.lean `tables_poly`: 7 step comments, numbered [1, 2, 3, 4, 5, 6, 7] (consecutive from 1: True), head lines [254, 266, 281, 291, 311, 321, 324]
  Yao/HybridProof/FakeSimulatorFactory.lean `exists_data`: 3 step comments, numbered [1, 2, 3] (consecutive from 1: True), head lines [91, 115, 141]
  Yao/HybridProof/SeedCoordinates.lean `pick_iff_place`: 4 step comments, numbered [1, 2, 3, 4] (consecutive from 1: True), head lines [250, 269, 287, 300]
  Yao/HybridProof/SelectedLaw.lean `acceptProb_fill`: 7 step comments, numbered [1, 2, 3, 4, 5, 6, 7] (consecutive from 1: True), head lines [83, 95, 101, 111, 132, 144, 156]
  LE-steps message, without the trailer lines:
    > Gate 42 G42-03 (minor, the documentation part of SY-F09): six proofs of at least 40 lines had
    > a proof sketch but no step comments (policy §3, "long proofs get step comments"). Each gains
    > brief `-- Step k: ...` comments at its major blocks, tying them to the existing sketch:
    > - Yao.lean `yaoHybrid_polyTime` (inside the approved body region): Alice's garbling
    >   program and layout, Bob's evaluator and layout, `HybridProtocol.polyTime_iff`, the two
    >   OT call-input machines, the message envelope (8 steps).
    > - SelectedLaw `acceptProb_fill`: coordinate split, matched exchange, seed and filled-seed
    >   readers, the two transports and the exchange's acceptance law (7 steps).
    > - FakeSimulatorFactory `exists_data`: construction and the two constructor equations (3).
    > - SeedCoordinates `pick_iff_place`: key summand, the two mixed cases, nonce summand (4).
    > - FakeProgram `tables_poly`: pieces, efficiency, assembler, context transport, record
    >   lookup, fan-in normalization, row identification (7).
    > - BobIO `outputBit_poly`: projections, vertex, key, pair, comparisons, agreement (6).
    > Comments only: whole comment lines inserted at code indentation, no tactic, term,
    > indentation or line break of code changed; stripping comments gives identical code.
    > 
controls (each a copy of the commit's first touched file):
  LE-reuse-2 on RunWithHost.lean: one added tactic caught by the comment-strip check True; one doubled space caught True; one inserted code line `skip` caught by the comment-strip check True and by the comment-line rule True (expected True each)
  LE-refs on ChunkScanner.lean: one added tactic caught by the comment-strip check True; one doubled space caught True; one inserted code line `skip` caught by the comment-strip check True and by the comment-line rule True (expected True each)
  LE-steps on Yao.lean: one added tactic caught by the comment-strip check True; one doubled space caught True; one inserted code line `skip` caught by the comment-strip check True and by the comment-line rule True (expected True each)

widths at the head over the 70 files: max 100 (at most 100: True); Yao.lean 1195 lines (SY-2 cap 1200: True); largest other file (649, 'RowFromCoins.lean')
  Yao.lean: 1179 -> 1195 lines, max width 99
  Yao/HybridProof/BobIO.lean: 243 -> 250 lines, max width 100
  Yao/HybridProof/ChunkScanner.lean: 294 -> 297 lines, max width 100
  Yao/HybridProof/FakeProgram.lean: 392 -> 405 lines, max width 100
  Yao/HybridProof/FakeSimulatorFactory.lean: 234 -> 237 lines, max width 100
  Yao/HybridProof/GarblingProgram.lean: 136 -> 138 lines, max width 99
  Yao/HybridProof/RunWithHost.lean: 209 -> 214 lines, max width 99
  Yao/HybridProof/SeedCoordinates.lean: 372 -> 380 lines, max width 100
  Yao/HybridProof/SelectedLaw.lean: 159 -> 168 lines, max width 100
`sorry` tokens outside comments in the 70 files: round 1 0, round 2 0

## ===== verification-r2.zip:checks/decls-r2.txt (this pack) =====

all 70 PR files, round 1 e9b03c43 -> round 2 355a0288
declarations: 856 -> 856; files whose declaration list (names, order) changed: []
headers differing: []; definition blocks differing: []; declaration docstrings differing: ['RunWithHost.lean:acc_poly']
files whose code differs after stripping comments: ['Yao/HybridProof/RunWithHost.lean']
  RunWithHost.lean, comment-stripped, outside acc_poly's span: identical True
module docstrings changed: ['Yao/HybridProof/ChunkScanner.lean', 'Yao/HybridProof/GarblingProgram.lean']
new declaration names in round 2: []

## ===== verification-r2.zip:checks/frozen-r2.txt (this pack) =====

=== TCSlib/Cryptography/SecureComputation/Yao.lean: tip f9fda8fe (970 lines) -> head 355a0288 (1195 lines; SY-2 cap 1200: True; max width 99)
approved regions (1-based line ranges, tip | head):
  hub import                       tip 10-9 (0 lines) | head 10-10 (1 lines)
  title line (LE-title)            tip 16-16 (1 lines) | head 17-17 (1 lines)
  Main results bullet              tip 98-99 (2 lines) | head 99-101 (3 lines)
  yaoHybrid_polyTime sketch        tip 854-868 (15 lines) | head 856-862 (7 lines)
  yaoHybrid_polyTime body          tip 871-871 (1 lines) | head 865-1008 (144 lines)
  yaoHybrid_simulators sketch      tip 888-934 (47 lines) | head 1025-1036 (12 lines)
  yaoHybrid_simulators body        tip 946-946 (1 lines) | head 1048-1171 (124 lines)
masked tip = masked head (everything outside the regions byte-identical): True; violations 0
rule breaks (column-0 line or sorry in a body, "not yet stated" in a sketch, hub import not one line): 0 []
unmasked diff hunks: 7; each inside one region on both sides:
  insert  tip 10-9 head 10-10: ['hub import']
  replace tip 16-16 head 17-17: ['title line (LE-title)']
  replace tip 98-99 head 99-101: ['Main results bullet']
  replace tip 854-868 head 856-862: ['yaoHybrid_polyTime sketch']
  replace tip 871-871 head 865-1008: ['yaoHybrid_polyTime body']
  replace tip 888-934 head 1025-1036: ['yaoHybrid_simulators sketch']
  replace tip 946-946 head 1048-1171: ['yaoHybrid_simulators body']
declarations: tip 76 (4 private), head 76; same names in the same order: True
  headers differing: []; definition blocks differing: []; docstrings differing: ['yaoHybrid_polyTime', 'yaoHybrid_simulators']
  yaoHybrid_polyTime: statement prose before **Proof sketch.** byte-identical: True (4 lines); header byte-identical: True
  yaoHybrid_simulators: statement prose before **Proof sketch.** byte-identical: True (14 lines); header byte-identical: True
  yaoSeed_good_whp: docstring, header and body byte-identical: True
  imports: tip 5, head 6; added ['import TCSlib.Cryptography.SecureComputation.Yao.HybridProof']; removed []
controls (each a copy of the head; expected violations, rule breaks):
  one character in a frozen header (yaoHybrid_hbcSecure): violations 1, rule breaks 0 (expected 1, 0): OK
  one extra line in a frozen region (above yaoSeed_good_whp): violations 1, rule breaks 0 (expected 1, 0): OK
  a second new import line: violations 1, rule breaks 0 (expected 1, 0): OK
  a declaration smuggled into the polyTime body: violations 0, rule breaks 1 (expected 0, 1): OK
  an edit inside a sketch (allowed): violations 0, rule breaks 0 (expected 0, 0): OK
  one doubled space in yaoHybrid_simulators' statement prose (head line 1012): violations 1, rule breaks 0 (expected 1, 0): OK

=== TCSlib/Cryptography/SecureComputation/Yao.lean: round 1 e9b03c43 (1179 lines) -> round 2 355a0288 (1195 lines): 8 hunks
  insert  round 1 865-864 round 2 865-866: ['yaoHybrid_polyTime body']; lines ['-- Step 1: Alice is efficient. The generic garbling program ', "-- uniform circuit description and the seed's key, nonce and"]
  insert  round 1 895-894 round 2 897-898: ['yaoHybrid_polyTime body']; lines ['-- Step 2: the interactive-layout constructor covers every h', '-- garbling on the empty history and echoes the first receiv']
  insert  round 1 900-899 round 2 904-905: ['yaoHybrid_polyTime body']; lines ['-- Step 3: Bob is efficient. The generic evaluator computes ', '-- messages and answers.']
  insert  round 1 930-929 round 2 936-937: ['yaoHybrid_polyTime body']; lines ['-- Step 4: the interactive-layout constructor covers every h', '-- first message.']
  insert  round 1 935-934 round 2 943-944: ['yaoHybrid_polyTime body']; lines ['-- Step 5: by `HybridProtocol.polyTime_iff`, it remains to g', '-- machines and the message envelope.']
  insert  round 1 940-939 round 2 950-951: ['yaoHybrid_polyTime body']; lines ["-- Step 6: for call `(i, t)`, Alice's OT input machine reads", "-- `inA + i` from the seed's coin blocks, through the finite"]
  insert  round 1 952-951 round 2 964-965: ['yaoHybrid_polyTime body']; lines ["-- Step 7: for call `(i, t)`, Bob's OT input machine reads h", '-- finite-product call index.']
  insert  round 1 959-958 round 2 973-974: ['yaoHybrid_polyTime body']; lines ["-- Step 8: the truncation bounds on ciphertexts bound Alice'", '-- `outLen` bits, and the two-move bound gives an envelope i']
  polyTime body region: round 1 865-992 (128 lines) -> round 2 865-1008 (144 lines); identical after stripping comments: True
  the polyTime sketch is unchanged since round 1: True
  masked round 1 = masked round 2 (all seven regions): True
TCSlib/Complexity/CircuitComplexity/Uniform.lean: blob at round 1 = round 2: True; TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean: blob at the tip = round 2: True

## ===== verification-r2.zip:checks/steps-r2.txt (this pack) =====

the six proofs of G42-03 at the head: the **Proof sketch.** (the docstring from the marker) and the step comments (line numbers at the head); for each backticked name in a step comment, where it occurs in the proof's code

=== Yao.lean `yaoHybrid_polyTime` (head lines 863-1008; proof lines at round 1 130, at round 2 146); docstring unchanged since round 1: True
  sketch:
    | **Proof sketch.** The generic garbling program computes Alice's message from the uniform
    | circuit description and the seed's key, nonce and shift readers. The generic evaluator
    | computes Bob's reply from arbitrary messages and answers. The interactive-layout
    | constructor handles every history: Alice sends the garbling or echoes the first message,
    | and Bob evaluates the first message. The two OT input machines read the appropriate
    | coin blocks and choice bits through the finite-product call index. The truncation bounds
    | on ciphertexts give a message envelope independent of the supplied answers. -/
  step comments:
    865: -- Step 1: Alice is efficient. The generic garbling program computes her message from the
    866: -- uniform circuit description and the seed's key, nonce and shift readers.
    897: -- Step 2: the interactive-layout constructor covers every history: Alice sends this
    898: -- garbling on the empty history and echoes the first received message otherwise.
    904: -- Step 3: Bob is efficient. The generic evaluator computes his reply from arbitrary
    905: -- messages and answers.
    936: -- Step 4: the interactive-layout constructor covers every history: Bob evaluates its
    937: -- first message.
    943: -- Step 5: by `HybridProtocol.polyTime_iff`, it remains to give the two OT call-input
    944: -- machines and the message envelope.
    950: -- Step 6: for call `(i, t)`, Alice's OT input machine reads bit `t` of both keys of wire
    951: -- `inA + i` from the seed's coin blocks, through the finite-product call index.
    964: -- Step 7: for call `(i, t)`, Bob's OT input machine reads his choice bit `y_i`, through the
    965: -- finite-product call index.
    973: -- Step 8: the truncation bounds on ciphertexts bound Alice's message, Bob's reply has
    974: -- `outLen` bits, and the two-move bound gives an envelope independent of the answers.
    `HybridProtocol.polyTime_iff`: in the proof code True
    `(i, t)`: an expression, not a name
    `t`: in the proof code True
    `inA + i`: in the proof code False; last component `inA` in the proof code True
    `(i, t)`: an expression, not a name
    `y_i`: in the proof code False; last component `y_i` in the proof code False
    `outLen`: in the proof code True

=== Yao/HybridProof/SelectedLaw.lean `acceptProb_fill` (head lines 69-166; proof lines at round 1 89, at round 2 98); docstring unchanged since round 1: True
  sketch:
    | **Proof sketch.** Split the complete tape into its retained shift/unused-block parameter
    | and independent actual key/nonce values. Convert the value table and challenge into their
    | existing coordinate types. The seed's inverse reader identifies the original sample with
    | these coordinates, and the filled-seed reader identifies replacement with the matched
    | coordinate exchange. Apply that exchange's proved uniform acceptance law and transport
    | back through the two coordinate equivalences. -/
  step comments:
    83: -- Step 1: `e` splits the tape into the retained shift/unused-block parameter and the actual
    84: -- key/nonce values in their coordinate type; `c` converts the challenge likewise.
    95: -- Step 2: each parameter's permutations give the matched coordinate exchange `pick`/`place`.
    101: -- Step 3: the seed's inverse reader identifies the original sample with these coordinates.
    111: -- Step 4: the filled-seed reader identifies the replacement with the matched exchange.
    132: -- Step 5: transport the actual sampler through the tape equivalence `e`.
    144: -- Step 6: pointwise, the filled sampler is the exchanged one under `e.prodCongr c`.
    156: -- Step 7: transport through `e.prodCongr c`, apply the exchange's proved uniform acceptance
    157: -- law `CoordinateSwap.acceptProb_swap`, and return to the actual tape by Step 5.
    `e`: in the proof code True
    `c`: in the proof code True
    `pick`: in the proof code True
    `place`: in the proof code True
    `e`: in the proof code True
    `e.prodCongr c`: in the proof code True
    `e.prodCongr c`: in the proof code True
    `CoordinateSwap.acceptProb_swap`: in the proof code True

=== Yao/HybridProof/FakeSimulatorFactory.lean `exists_data` (head lines 83-166; proof lines at round 1 81, at round 2 84); docstring unchanged since round 1: True
  sketch:
    | **Proof sketch.** Construct the existing data value from the supplied fields. Apply each
    | of its pointwise constructor equations with every argument explicit. The resulting word
    | equations expose the dependent families together, without asking consumers to match them. -/
  step comments:
    91: -- Step 1: construct the existing data value from the supplied fields, every argument named.
    115: -- Step 2: answer words, by the pointwise constructor equation with every argument explicit.
    141: -- Step 3: message words, by the pointwise constructor equation with every argument explicit.

=== Yao/HybridProof/SeedCoordinates.lean `pick_iff_place` (head lines 239-321; proof lines at round 1 75, at round 2 83); docstring unchanged since round 1: True
  sketch:
    | **Proof sketch.** In the key summand there is one matching vertex/bit coordinate and one
    | challenge slot. Mixed summands cannot match. Within the nonce summand, injectivity of the
    | sum constructor reduces both directions to the existing nonce-coordinate inverse contract. -/
  step comments:
    250: -- Step 1: key summand. The only matching pair is the coordinate `(u, true)` and the single
    251: -- key slot.
    269: -- Step 2: mixed summands cannot match. A key label never picks a nonce slot, and `place`
    270: -- sends nonce slots only to nonce coordinates.
    287: -- Step 3: mixed summands cannot match. A nonce coordinate never picks the key slot, and
    288: -- `place` sends the key slot to a key label.
    300: -- Step 4: nonce summand. Injectivity of `Sum.inr` reduces both directions to the
    301: -- nonce-coordinate inverse contract `NonceCoordinates.pick_iff_place`.
    `(u, true)`: an expression, not a name
    `place`: in the proof code True
    `place`: in the proof code True
    `Sum.inr`: in the proof code True
    `NonceCoordinates.pick_iff_place`: in the proof code True

=== Yao/HybridProof/FakeProgram.lean `tables_poly` (head lines 227-333; proof lines at round 1 94, at round 2 107); docstring unchanged since round 1: True
  sketch:
    | **Proof sketch.** Decode the canonical circuit description to the public gate-record word.
    | At a unary index, select its argument-word list and invoke the real garbler's generic row
    | core with the constant false output bit. The existing guarded table adapter enumerates at
    | most four rows, and the indexed word-vector assembler traverses all gate records. To prove
    | correctness, transport the retained context through the generic pointwise table contract.
    | Canonical record lookup fixes the argument list. Its fan-in bound removes the guard and
    | normalizes the dependent assignment enumeration. The arbitrary-output-bit row theorem then
    | identifies every enumerated row with the new simulated semantic object. -/
  step comments:
    254: -- Step 1: the pieces: the decoded gate-record word, the argument-word list at a unary
    255: -- index, the real garbler's row core with constant false output bit, and the guarded
    256: -- table adapter.
    266: -- Step 2: each piece is polynomial-time; `hgs` reads the decoded word as the encoded gate
    267: -- records.
    281: -- Step 3: the indexed word-vector assembler traverses all gate records; it remains to
    282: -- identify each entry with its simulated table.
    291: -- Step 4: correctness. Transport the retained context through the generic pointwise table
    292: -- contract `tableWordWith_congr_at`.
    311: -- Step 5: canonical record lookup fixes the argument list.
    321: -- Step 6: the fan-in bound removes the guard and normalizes the assignment enumeration.
    324: -- Step 7: the arbitrary-output-bit row theorem identifies every enumerated row with the
    325: -- simulated row.
    `hgs`: in the proof code True
    `tableWordWith_congr_at`: in the proof code True

=== Yao/HybridProof/BobIO.lean `outputBit_poly` (head lines 99-149; proof lines at round 1 44, at round 2 51); docstring unchanged since round 1: True
  sketch:
    | **Proof sketch.** Use unary word-list lookup for the output vertex and the decoding pair.
    | The vertex's key is another word-list lookup, padded to the parameter length. Two word
    | comparisons implement the decoding rule. Each lookup and padding operation is total, so
    | malformed words require no separate machine. -/
  step comments:
    100: -- Step 1: the value list, decoding pairs and output vertices are projections of the context.
    114: -- Step 2: unary word-list lookup gives the output vertex.
    118: -- Step 3: the vertex's key is another word-list lookup, padded to the parameter length.
    128: -- Step 4: unary word-list lookup gives the decoding pair.
    132: -- Step 5: two word comparisons and a branch implement the decoding rule.
    143: -- Step 6: on every raw word the branch is `[outputBit z]`, by the reader `outputBit_eq`;
    144: -- every lookup and padding operation is total, so malformed words need no separate case.
    `[outputBit z]`: an expression, not a name
    `outputBit_eq`: in the proof code True

## ===== verification-r2.zip:checks/sources-r2.txt (this pack) =====

citation tags against the file's `## References` entries (an entry is a line `* [TAG] ...` in that section), over the 70 PR files
  round 1 e9b03c43: tags without an entry: 2 ['ChunkScanner.lean: [AB09]', 'GarblingProgram.lean: [BMR90]']
  round 2 355a0288: tags without an entry: 0 []
the library's reference entries for AB09 and BMR90 in the PR files at the head (each entry with its continuation line):
      TCSlib/Complexity/CircuitComplexity/Uniform.lean:79: * [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009. (§6.2; Definitions 6.12 and 6.14, Theorem 6.13.)
      Yao.lean:111: * [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*, STOC 1990, pp. 503–513 (the point-and-permute row order).
  NEW Yao/HybridProof/ChunkScanner.lean:30: * [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009, §6.2 (descriptions of uniform circuit families).
      Yao/HybridProof/CoinRelabel.lean:38: * [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*, STOC 1990, pp.503–513 (point-and-permute).
      Yao/HybridProof/DescriptionDecoder.lean:40: * [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009, §6.2 (descriptions of uniform circuit families).
  NEW Yao/HybridProof/GarblingProgram.lean:31: * [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*, STOC 1990, pp. 503–513 (point-and-permute row order of the garbled tables).
      Yao/HybridProof/RowFromCoins.lean:35: * [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*, STOC 1990, pp. 503–513 (point-and-permute row relabelling).
      Yao/HybridProof/RunWithHost.lean:38: * [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009, §6.1 (topologically ordered circuits).
registry blueprint/src/references/sources.json at the pin: AB09 registered True; BMR90 registered False; the registry file is the same blob at round 1's pin f22e0f67: True

## ===== verification-r2.zip:checks/integration-r2.txt (this pack) =====

briefs/pass-shelat-ch5-8/fills/sc-yao/final-r1/integration-tip/ at the records pin 2da7e0f3: README.md 17729 bytes (sha256 a57c0d409c592c271cbcf3c9207aac60b20584f765a7dd3690a5c67ef0a25975); SHA256SUMS 134838 bytes (sha256 501920db1bb3eaf89995424bb6e719573be71e3730d156a8e290b99912a628f7); integration-tip-evidence.zip 3528629 bytes, sha256 4d24501bca1d67a8cf8905448acb77b161a61a45e8d38f72f14dea2fca95d6d8
  the working tree copies equal the pin's blobs: True
  SHA256SUMS rows 990: 989 entries plus the ZIP itself (True); ZIP entries 989, path set = the manifest's: True; directories 0
  every entry hashes to its manifest row: True (mismatches [])

M and M' (the README, merge/merge-facts.txt, mprime/merge/merge-facts.txt) rebuilt from git objects:
  M: git merge-tree --write-tree f22e0f67 e9b03c43 -> 741bafe2ce706adbf697ab893bf4bc28e7eb1d7d (rc 0); = the recorded tree 741bafe2ce706adbf697ab893bf4bc28e7eb1d7d: True; the recorded commit e327a5f2 is local only (not pushed); present here: True, tree 741bafe2ce706adbf697ab893bf4bc28e7eb1d7d, parents f22e0f6798815b9263893e61928b4f16452f74ee e9b03c437aca251846430ff23b40ee5ff3d3347a
  M': git merge-tree --write-tree f22e0f67 355a0288 -> 84c5381ba7188069f296f899efff9104f9b9bbe0 (rc 0); = the recorded tree 84c5381ba7188069f296f899efff9104f9b9bbe0: True; the recorded commit 061ad60c is local only (not pushed); present here: True, tree 84c5381ba7188069f296f899efff9104f9b9bbe0, parents f22e0f6798815b9263893e61928b4f16452f74ee 355a0288d56290e8c984228cbc1824187029e456
  M' is the merge of 355a0288 into T = f22e0f67 (parents T and 355a0288), not a merge of M: True; its tree differs from M's exactly by the round-1 -> round-2 diff:
    git diff --raw 741bafe2 84c5381b (trees M, M') = git diff --raw e9b03c43 355a0288: True (9 paths)
    = the ZIP's mprime/merge/diff-M-Mprime.raw and diff-e9b03c43-355a0288.raw: True True
    git diff --raw 201bf57a M' over TCSlib, TCSlib.lean, audits = git diff --raw f9fda8fe 355a0288: True (70 paths); = the ZIP's diff-f9fda8fe-355a0288.raw True

M build (build-m/results.jsonl): 772 module records; rc 0 and 0 errors in all: True; sorry warnings 89; every record's source_sha256 = its file in the tree of M: True; root TCSlib and both audits Checks among them: True
  the built set = the downstream (in M's tree) of every module changed since the olean snapshot base eff2dcd0: True (772 modules)
  build-m/statecheck.txt last lines: ['e327a5f2 order 1410; bad 0 []', 'RESULT OK']; build-m/refunion.txt: summary modules 772; byte-identical (source and olean) to at least one reference 772; none 0; modules with a same-source different-olean reference 2
  admissions/census-tip-vs-M-summary.txt: tip (201bf57a Lean = f22e0f67 Lean) census equals int-x X1 census per module: True | tip total 229; M total 227 | CHANGED TCSlib/Cryptography/SecureComputation/Yao 2 -> 0 | new modules at M 68, all with 0: True | removed modules [] | no record at M: 34 (same set as tip: True )
M' build (mprime/build/results.jsonl): 20 module records and 1 "done" record; rc 0 and 0 errors in all: True; sorry 0; warnings 1 (['BobIO'])
  the 20 built modules = the modules of the tree of M' whose import closure meets the 9 changed files (computed from git objects, 1444 modules of TCSlib and audits): True; extra [], missing []
  every record's source_sha256 = the sha256 of its file in the tree of M': True; and the 9 changed files there = their blobs at 355a0288: True
  raw logs mprime/build/mods/: 20; each log's sha256 = its record's log_sha256: True; error lines (both forms) 0; substring "error" 0; non-empty logs ['TCSlib_Cryptography_SecureComputation_Yao_HybridProof_BobIO.log']
  the BobIO warning: "TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean:218:37: warning: try 'simp' instead of 'simpa'"; line 218 of BobIO.lean at the head: 'rw [List.getD_eq_getElem _ _ (by simpa using j.isLt), List.getElem_ofFn]' (round 1 line 211: 'rw [List.getD_eq_getElem _ _ (by simpa using j.isLt), List.getElem_ofFn]')
  mprime/build/buildsum.txt: modules 20; rc!=0 []; errors (G26-N1 form) 0; error substring 0; sorry warnings 0; warnings 1; seconds 159
  mprime/build/permod.out: modules 20; rc!=0 0; error: 0; error( 0; combined 0; substring 0; sorry 0; warnings 1; log/record mismatches []
  mprime/plan/plan.out: plan 061ad60c: order 1410; build 20; reuse 1390
  mprime/build/stateupdate.out: update 061ad60c: 20 modules; not taken []
  mprime/build/statecheck.txt: 1410 OK lines, other module lines 0; last lines ['061ad60c order 1410; bad 0 []', 'RESULT OK']
  admissions: census M 'TOTAL 227 sorry warnings over 1410 modules with a matching rec'; census M' 'TOTAL 227 sorry warnings over 1410 modules with a matching rec'; modules 1410 and 1410; per-module counts equal: True; nonzero at M' in the PR's modules: []

axioms at M' (mprime/axioms-summary-AxiomsLand.txt, mprime/axioms-summary-AxiomsLE.txt):
  mprime/axioms-summary-AxiomsLand.txt: 25 constants, nonstandard []; yaoProtocol_hbcSecure :: propext, Classical.choice, Quot.sound; ADMITTED yaoHybrid_polyTime: closure 9172; direct sorryAx 0: []; ADMITTED yaoHybrid_simulators: closure 20202; direct sorryAx 0: []; ADMITTED yaoHybrid_hbcSecure: closure 20479; direct sorryAx 0: []; ADMITTED yaoProtocol_hbcSecure: closure 21457; direct sorryAx 0: []; ADMITTED yaoSeed_good_whp: closure 17757; direct sorryAx 0: []; CENSUS stored 1492; nonstandard 0; simp-lemmas 27; instances 11
  mprime/axioms-summary-AxiomsLE.txt: 2 constants, nonstandard []; YaoHybridProof.RunWithHost.acc_poly :: propext, Classical.choice, Quot.sound; Complexity.StateLoop.MajLoop.acc_poly :: propext, Classical.choice, Quot.sound; ADMITTED YaoHybridProof.RunWithHost.acc_poly: closure 4610; direct sorryAx 0: []
  mprime/axioms-vs-M.diff: 10 lines, only closure sizes: True
  the probe AxiomsLE.lean (mprime/probe-src/), its commands: ['#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly', '#admitted TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly', '#print axioms Complexity.StateLoop.MajLoop.acc_poly', '#check @TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly', '#check @Complexity.StateLoop.MajLoop.acc_poly', '#check @TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_eq', '#check @Complexity.StateLoop.MajLoop.acc_eq']
  its raw log (mprime/probe-runs/mods/ScYaoLEProbe_AxiomsLE.log), the #check output included:
    | 'TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly' depends on axioms: [propext,
    |  Classical.choice,
    |  Quot.sound]
    | ADMITTED TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly: closure 4610; direct sorryAx 0: []
    | 'Complexity.StateLoop.MajLoop.acc_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
    | TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly : Complexity.PolyTimeComputable fun w =>
    |   [TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc w]
    | Complexity.StateLoop.MajLoop.acc_poly : Complexity.PolyTimeComputable fun v => [Complexity.StateLoop.MajLoop.acc v]
    | TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_eq : ∀ (w : List Bool),
    |   TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc w =
    |     decide (Complexity.pairFstD (Complexity.pairSndD w) = [])
    | Complexity.StateLoop.MajLoop.acc_eq : ∀ (v : List Bool),
    |   Complexity.StateLoop.MajLoop.acc v = decide (Complexity.pairFstD (Complexity.pairSndD v) = [])
  M (axioms-summary-AxiomsLand.txt, the integration before the landing edits): yaoProtocol_hbcSecure line ['yaoProtocol_hbcSecure :: propext, Classical.choice, Quot.sound', 'ADMITTED yaoProtocol_hbcSecure: closure 21453; direct sorryAx 0: []']

RunWithHost seals at M' (mprime/seals-{coe,strict}/{A,B}/, mprime/seal-runs/):
  coe A: probe sha256 = manifest probe_sha256 = run record source_sha256: True; manifest rev 061ad60c (= M' True); removing the 3 recorded insertions (each hash checked: True) gives RunWithHost.lean at 355a0288 byte for byte: True; requests 844 = rows 844; raw log: error: 0, error( 0, install True, eof True, SEAL-END requested = verified True; record rc 0, log sha256 = record True; Complexity.StateLoop.MajLoop.acc sealed True, its term readers ['TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly']; notation exclusions ['Complexity.PolyExpr.eval', 'TCSlib.InformationTheory.FinDist.instCoeFunForallReal']
  coe B: probe sha256 = manifest probe_sha256 = run record source_sha256: True; manifest rev 061ad60c (= M' True); removing the 3 recorded insertions (each hash checked: True) gives RunWithHost.lean at 355a0288 byte for byte: True; requests 845 = rows 845; raw log: error: 0, error( 0, install True, eof True, SEAL-END requested = verified True; record rc 0, log sha256 = record True; Complexity.StateLoop.MajLoop.acc sealed True, its term readers ['TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly']; notation exclusions ['TCSlib.InformationTheory.FinDist.instCoeFunForallReal']
  strict A: probe sha256 = manifest probe_sha256 = run record source_sha256: True; manifest rev 061ad60c (= M' True); removing the 3 recorded insertions (each hash checked: True) gives RunWithHost.lean at 355a0288 byte for byte: True; requests 844 = rows 844; raw log: error: 0, error( 0, install True, eof True, SEAL-END requested = verified True; record rc 0, log sha256 = record True; Complexity.StateLoop.MajLoop.acc sealed True, its term readers ['TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly']; notation exclusions ['Complexity.PolyExpr.eval']
  strict B: probe sha256 = manifest probe_sha256 = run record source_sha256: True; manifest rev 061ad60c (= M' True); removing the 3 recorded insertions (each hash checked: True) gives RunWithHost.lean at 355a0288 byte for byte: True; requests 845 = rows 845; raw log: error: 0, error( 0, install True, eof True, SEAL-END requested = verified True; record rc 0, log sha256 = record True; Complexity.StateLoop.MajLoop.acc sealed True, its term readers ['TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost.acc_poly']; notation exclusions []
  coe and strict probes byte-identical: A True, B True (no projection-coercion instance in this file's closure)

Yao.lean seals (int-tip/seal-*): run at M, not at M':
  coe A: manifest rev e327a5f2 (= M True); seal-sum-coe-A.tsv: ['3046', '0', '0'] (requests, rc, errors)
  coe B: manifest rev e327a5f2 (= M True); seal-sum-coe-B.tsv: ['3047', '1', '24'] (requests, rc, errors)
  seal-compare-phase2.txt: coe A: Phase 2 0 errors; M 0 errors (error: 0, error( 0); error positions identical True; whole log identical after the probe-directory rename True; install/EOF markers True/True | coe B: Phase 2 24 errors; M 24 errors (error: 24, error( 0); error positions identical True; whole log identical after the probe-directory rename True; install/EOF markers True/True
  Yao.lean at M = at e9b03c43: True; Yao.lean at M' = at 355a0288: True; the two differ by comment lines only (le-r2.txt, frozen-r2.txt): True
  files of the landing edits with no seal at M' (comment-only, le-r2.txt): ['Yao.lean', 'Yao/HybridProof/BobIO.lean', 'Yao/HybridProof/ChunkScanner.lean', 'Yao/HybridProof/FakeProgram.lean', 'Yao/HybridProof/FakeSimulatorFactory.lean', 'Yao/HybridProof/GarblingProgram.lean', 'Yao/HybridProof/SeedCoordinates.lean', 'Yao/HybridProof/SelectedLaw.lean']

## ===== verification-r2.zip:checks/closure-r2.txt (this pack) =====

the import closure of the 70 changed modules: at round 1 262 files, at round 2 262; same path set True; import lines of the 70 files unchanged: True
round 1's sources.zip: 262 TCSlib files; = the closure path set: True
  files whose blob at 355a0288 equals round 1's sources.zip member: 253; differing: 9 = the 9 files of the round-2 diff: True
  TCSlib/Complexity/Randomized/Build/StringLoops.lean at 355a0288 = at the records pin = at f9fda8fe = round 1's member: True
  shortest import chain RunWithHost -> StringLoops at 355a0288: ['Cryptography/SecureComputation/Yao/HybridProof/RunWithHost', 'Complexity/Randomized/Repetition', 'Complexity/Randomized/Build/StringLoops']
  StringLoops `acc` (line 97): def acc (v : List Bool) : Bool := decide (pairFstD (pairSndD v) = []) ...
  StringLoops `acc_eq` (line 100): theorem acc_eq (v : List Bool) : acc v = decide (pairFstD (pairSndD v) = []) ...
  StringLoops `acc_poly` (line 144): theorem acc_poly : PolyTimeComputable fun v => [acc v] ...
  the two acceptance predicates, bound variable renamed: RunWithHost.acc `decide (pairFstD (pairSndD x) = [])` | MajLoop.acc `decide (pairFstD (pairSndD x) = [])`; equal True

## ===== verification-r2.zip:checks/mergetrees-r2.txt (this pack) =====

git merge-tree --write-tree 2da7e0f3 (records pin) 355a0288: rc 0, tree 583049b02e8b08c5a3074ebcbaffd7969da8ef11; the merged tree differs from the pin in exactly the PR's 70 paths: True
  its TCSlib, TCSlib.lean, audits subtrees = those of M' (84c5381b): True
#331 head 9e7a9648: merge-tree with 355a0288 rc 0 (clean True); its own paths since its merge base with the pin 13; shared with #341's 70: []
#338 head d45d3682: merge-tree with 355a0288 rc 0 (clean True); its own paths since its merge base with the pin 2; shared with #341's 70: []
#339 head 839f36cc: merge-tree with 355a0288 rc 0 (clean True); its own paths since its merge base with the pin 5; shared with #341's 70: []
open PRs on the records branch (GitHub, 2026-11-16): #341, #339, #338, #331; #340 is no longer open and not merged into the pin

## ===== verification-r2.zip:checks/lint-r2.txt (this pack) =====

scripts/campaign_style_lint.py at the records pin 2da7e0f3 (sha256 016c1cb71e3f9c8ac96719756eb743b9579ca7a7a09eb810dddd668c33fcfa98; the same blob at both heads: True), run as `python3 -I scripts/campaign_style_lint.py TCSlib --check8b` in a mini tree holding only the 70 PR files
round 1 e9b03c43: exit 0; style_lint: 0 FAIL, 2 WARN over 70 files
  WARN TCSlib/Complexity/CircuitComplexity/Uniform.lean 1 public def(s) without a lemma beside them (check 8): IsPUniform
  WARN TCSlib/Cryptography/SecureComputation/Yao.lean 1179 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
round 2 355a0288: exit 0; style_lint: 0 FAIL, 2 WARN over 70 files
  WARN TCSlib/Complexity/CircuitComplexity/Uniform.lean 1 public def(s) without a lemma beside them (check 8): IsPUniform
  WARN TCSlib/Cryptography/SecureComputation/Yao.lean 1195 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
FAIL and WARN lines identical in the two runs: False; added ['WARN TCSlib/Cryptography/SecureComputation/Yao.lean 1195 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)']; removed ['WARN TCSlib/Cryptography/SecureComputation/Yao.lean 1179 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)']
identical once the line count in the size WARN is masked: True (Yao.lean 1179 -> 1195 lines, SY-2 cap 1200); no FAIL in either run

## ===== briefs/pass-shelat-ch5-8/gates/42-sc-yao/pr-r2.diff.txt (this pack) =====

diff --git a/TCSlib/Cryptography/SecureComputation/Yao.lean b/TCSlib/Cryptography/SecureComputation/Yao.lean
index 47d4c268f..fb898170f 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao.lean
@@ -862,6 +862,8 @@ coin blocks and choice bits through the finite-product call index. The truncatio
 on ciphertexts give a message envelope independent of the supplied answers. -/
 theorem yaoHybrid_polyTime (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
     (yaoHybrid Y E₁ E₂).PolyTime (yaoFunctionality Y) := by
+  -- Step 1: Alice is efficient. The generic garbling program computes her message from the
+  -- uniform circuit description and the seed's key, nonce and shift readers.
   open YaoHybridProof in
   have hAlice : (yaoAlice Y E₁ E₂).Efficient := by
     obtain ⟨gen, hgen, hgenEq⟩ := Y.uniform
@@ -892,11 +894,15 @@ theorem yaoHybrid_polyTime (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeCo
       (fun _ => Nat.le_add_right _ _) (fun w => Y.outs_lt _) (fun w => hfan _)
       (fun w v hv b => by rw [keyAt_yaoSeed Y _ _ hv]; rfl)
       (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
+    -- Step 2: the interactive-layout constructor covers every history: Alice sends this
+    -- garbling on the empty history and echoes the first received message otherwise.
     apply firstThenEcho_efficient (yaoAlice Y E₁ E₂)
       (fun x z r => yaoMsg Y E₁ E₂ x.length (pairFstD z) r)
       (yaoAlice_next_nil Y E₁ E₂) (yaoAlice_next_cons Y E₁ E₂)
     refine hp.congr fun w => ?_
     simp only [yaoMsg_eq, yaoTables_eq, yaoKeysA_eq, yaoPairs_eq, encodeMsgs_eq_encWords]
+  -- Step 3: Bob is efficient. The generic evaluator computes his reply from arbitrary
+  -- messages and answers.
   have hBob : (yaoBob Y E₁ E₂).Efficient := by
     obtain ⟨gen, hgen, hgenEq⟩ := Y.uniform
     have hdesc n : gen (List.replicate n true) = pairEncode (Y.circ n).encode
@@ -927,16 +933,22 @@ theorem yaoHybrid_polyTime (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeCo
         · rfl)
       (fun w => by simp only [yaoBobInit_eq, List.length_ofFn])
       (fun w v => by simp only [yaoBobTables_eq]; rfl) (fun _ => rfl)
+    -- Step 4: the interactive-layout constructor covers every history: Bob evaluates its
+    -- first message.
     apply reply_efficient (yaoBob Y E₁ E₂)
       (fun x z a => yaoBobOut Y E₁ E₂ x.length a (pairSndD z))
       (yaoBob_next Y E₁ E₂)
     refine hp.congr fun w => ?_
     simp only [yaoBobOut_eq, yaoBobValues_eq, decodeOut_eq, msg, ans]
+  -- Step 5: by `HybridProtocol.polyTime_iff`, it remains to give the two OT call-input
+  -- machines and the message envelope.
   apply (HybridProtocol.polyTime_iff (yaoHybrid Y E₁ E₂) (yaoFunctionality Y)).mpr
   refine ⟨hAlice, hBob,
     ⟨OTInputs.otInputA Y.inA Y.sizeBound,
       OTInputs.polyTimeComputable_otInputA Y.inA Y.sizeBound, ?_⟩,
     ⟨OTInputs.otInputB, OTInputs.polyTimeComputable_otInputB, ?_⟩, ?_⟩
+  -- Step 6: for call `(i, t)`, Alice's OT input machine reads bit `t` of both keys of wire
+  -- `inA + i` from the seed's coin blocks, through the finite-product call index.
   · intro n x r j
     have hlen : otFunctionality.inA.eval n = 2 := by
       rw [otFunctionality_inA, PolyExpr.eval_const]
@@ -949,6 +961,8 @@ theorem yaoHybrid_polyTime (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeCo
       have := i.isLt
       omega), readBits_apply]
     simp only [Nat.add_assoc]
+  -- Step 7: for call `(i, t)`, Bob's OT input machine reads his choice bit `y_i`, through the
+  -- finite-product call index.
   · intro n x r j
     have hlen : otFunctionality.inB.eval n = 1 := by
       rw [otFunctionality_inB, PolyExpr.eval_const]
@@ -956,6 +970,8 @@ theorem yaoHybrid_polyTime (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeCo
     apply CallEquations.inputB_eq n (Y.inB.eval n) x r
     intro i t c
     rw [yaoHybrid_callB, yaoCall_finProdFinEquiv]
+  -- Step 8: the truncation bounds on ciphertexts bound Alice's message, Bob's reply has
+  -- `outLen` bits, and the two-move bound gives an envelope independent of the answers.
   · have hfan n (i : Fin (Y.circ n).gates.length) :
         ((Y.circ n).gates[i]).args.length ≤ 2 :=
       ((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _
diff --git a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean
index 63af3311b..baa57d109 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean
@@ -97,6 +97,7 @@ The vertex's key is another word-list lookup, padded to the parameter length. Tw
 comparisons implement the decoding rule. Each lookup and padding operation is total, so
 malformed words require no separate machine. -/
 theorem outputBit_poly : PolyTimeComputable fun z => [outputBit z] := by
+  -- Step 1: the value list, decoding pairs and output vertices are projections of the context.
   let ctx := pairFstD
   let vals := fun z => pairFstD (pairSndD (ctx z))
   let pairs := fun z => pairFstD (pairSndD (pairSndD (ctx z)))
@@ -110,9 +111,11 @@ theorem outputBit_poly : PolyTimeComputable fun z => [outputBit z] := by
   have ho : PolyTimeComputable outs :=
     polyTimeComputable_pairSndD.comp
       (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hc))
+  -- Step 2: unary word-list lookup gives the output vertex.
   let vertex := fun z => BinArith.uHead (BinArith.getW (pairEncode (pairSndD z) (outs z)))
   have hvertex : PolyTimeComputable vertex := BinArith.polyTimeComputable_uHead.comp
     (BinArith.polyTimeComputable_getW.comp (polyTimeComputable_pairSndD.pairEncode ho))
+  -- Step 3: the vertex's key is another word-list lookup, padded to the parameter length.
   let key := fun z => EnsembleLemmas.padL (pairFstD (ctx z)).length
     (BinArith.getW (pairEncode (vertex z) (vals z)))
   have hk0 := EnsembleLemmas.polyTimeComputable_padL .var
@@ -122,9 +125,11 @@ theorem outputBit_poly : PolyTimeComputable fun z => [outputBit z] := by
     (BinArith.polyTimeComputable_getW.comp' (hvertex.pairEncode hv))
   have hk : PolyTimeComputable key := hk0.congr (g := key) fun z => by
     simp only [key, PolyExpr.eval_var]
+  -- Step 4: unary word-list lookup gives the decoding pair.
   let pair := fun z => BinArith.getW (pairEncode (pairSndD z) (pairs z))
   have hpair : PolyTimeComputable pair :=
     BinArith.polyTimeComputable_getW.comp (polyTimeComputable_pairSndD.pairEncode hp)
+  -- Step 5: two word comparisons and a branch implement the decoding rule.
   have heq0 : PolyTimeComputable fun z => [decide (key z = pairFstD (pair z))] :=
     (polyTimeComputable_pairEq.comp
       (hk.pairEncode (polyTimeComputable_pairFstD.comp hpair))).congr fun z => by
@@ -135,6 +140,8 @@ theorem outputBit_poly : PolyTimeComputable fun z => [outputBit z] := by
         simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
   refine (polyTimeComputable_ite heq0 (polyTimeComputable_const [false]) heq1).congr
     (g := fun z => [outputBit z]) ?_
+  -- Step 6: on every raw word the branch is `[outputBit z]`, by the reader `outputBit_eq`;
+  -- every lookup and padding operation is total, so malformed words need no separate case.
   intro z
   by_cases h : key z = pairFstD (pair z) <;>
     simp only [outputBit_eq, ctx, vals, pairs, outs, vertex, key, pair] at h ⊢ <;>
diff --git a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean
index 9f7398f83..60df96832 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean
@@ -27,6 +27,9 @@ The circuit-description decoder uses its seven control phases.
 
 ## References
 
+* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
+  Cambridge University Press, 2009, §6.2 (descriptions of uniform circuit families).
+
 Generic parsing infrastructure for [AB09, §6.2], circuit descriptions. The machine assembly
 uses the emitting-loop host of `Complexity.polyTimeComputable_emitIter`.
 -/
diff --git a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean
index ab14ee695..87574910c 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean
@@ -251,6 +251,9 @@ theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeCompu
       ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
     PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun i =>
       BinArith.encWords (FakeObjects.table (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i)) := by
+  -- Step 1: the pieces: the decoded gate-record word, the argument-word list at a unary
+  -- index, the real garbler's row core with constant false output bit, and the guarded
+  -- table adapter.
   let gates := GarblingProgram.gatesWord description
   let record := fun w => BinArith.getW (pairEncode (pairFstD w) (gates (pairSndD w)))
   let args := fun w => pairSndD (record w)
@@ -260,6 +263,8 @@ theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeCompu
     args (fun w => coins (pairSndD w)) (fun _ => false) l a
   let entry := TablesFromCoins.tableWordWith args row
   let entryVal := fun z i => entry (pairEncode (List.replicate i true) z)
+  -- Step 2: each piece is polynomial-time; `hgs` reads the decoded word as the encoded gate
+  -- records.
   have hgates : PolyTimeComputable gates := GarblingProgram.gatesWord_poly hdescription
   have hgs (z : List Bool) :
       gates z = BinArith.encWords ((C z).gates.map DescriptionDecoder.gateRecord) :=
@@ -273,6 +278,8 @@ theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeCompu
       (hinputs.comp polyTimeComputable_pairSndD)
       (unaryLength_poly polyTimeComputable_pairFstD) hargs
       (hcoins.comp polyTimeComputable_pairSndD) (polyTimeComputable_const [false]) l a)
+  -- Step 3: the indexed word-vector assembler traverses all gate records; it remains to
+  -- identify each entry with its simulated table.
   have hcount : PolyTimeComputable fun z => List.replicate (C z).gates.length true := by
     refine (BinArith.polyTimeComputable_countW.comp hgates).congr fun z => ?_
     rw [Function.comp_apply, BinArith.countW_eq, hgs z,
@@ -281,6 +288,8 @@ theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeCompu
     hentry.comp ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).pairEncode
       polyTimeComputable_pairSndD)
   refine WordLists.ofFnTable_poly _ entryVal hcount he ?_
+  -- Step 4: correctness. Transport the retained context through the generic pointwise table
+  -- contract `tableWordWith_congr_at`.
   intro z i
   symm
   let w := pairEncode (List.replicate i true) z
@@ -299,6 +308,7 @@ theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeCompu
       List.length_replicate]
   change TablesFromCoins.tableWordWith args row w = _
   rw [TablesFromCoins.tableWordWith_congr_at args args' row row' w z ha hr]
+  -- Step 5: canonical record lookup fixes the argument list.
   have hrec : BinArith.getW (pairEncode (List.replicate i true) (gates z)) =
       DescriptionDecoder.gateRecord ((C z).gates[i]) := by
     rw [hgs z, BinArith.getW_pairEncode, List.length_replicate]
@@ -308,8 +318,11 @@ theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeCompu
       BinArith.encWords (((C z).gates[i]).args.map fun v => List.replicate v true) := by
     dsimp only [args']
     rw [hrec, DescriptionDecoder.gateRecord_eq, pairSndD_pairEncode]
+  -- Step 6: the fan-in bound removes the guard and normalizes the assignment enumeration.
   rw [TablesFromCoins.tableWordWith_of_encoded args' row' z _ (hfan z i) hcanonical,
     FakeObjects.table_eq]
+  -- Step 7: the arbitrary-output-bit row theorem identifies every enumerated row with the
+  -- simulated row.
   apply congrArg BinArith.encWords
   apply List.map_congr_left
   intro a _
diff --git a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulatorFactory.lean b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulatorFactory.lean
index 5e1451002..491c6174b 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulatorFactory.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulatorFactory.lean
@@ -88,6 +88,7 @@ theorem exists_data :
       ∀ n r f, FakeSimulator.messageAt d n r f =
         FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
           (inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false) := by
+  -- Step 1: construct the existing data value from the supplied fields, every argument named.
   refine ⟨FakeSimulator.Data.make
       (E₁ := E₁)
       (E₂ := E₂)
@@ -111,6 +112,7 @@ theorem exists_data :
       (nonce₀ := nonce₀)
       (nonce₁ := nonce₁)
       (permutation := permutation), ?_, ?_⟩
+  -- Step 2: answer words, by the pointwise constructor equation with every argument explicit.
   · intro n r
     exact FakeSimulator.Data.make_answersAt
       (E₁ := E₁)
@@ -136,6 +138,7 @@ theorem exists_data :
       (nonce₁ := nonce₁)
       (permutation := permutation)
       n r
+  -- Step 3: message words, by the pointwise constructor equation with every argument explicit.
   · intro n r f
     exact FakeSimulator.Data.make_messageAt
       (E₁ := E₁)
diff --git a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean
index 9b5fb60e2..e38807a09 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean
@@ -28,6 +28,8 @@ to any definition from `Yao.lean`.
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
   2010, Protocol 162.6 (garbling the canonical uniform circuit).
+* [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*,
+  STOC 1990, pp. 503–513 (point-and-permute row order of the garbled tables).
 -/
 
 namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram
diff --git a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean
index 083f74b7f..a09a9f84a 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean
@@ -84,10 +84,15 @@ theorem step_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
         (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))))
 
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
 
 /-- After `i ≤ |gs x|` rounds, the state is the unprocessed gate suffix paired with
 `valueCode x (runWith (f x) ((gs x).take i) (init x))`.
diff --git a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SeedCoordinates.lean b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SeedCoordinates.lean
index feb6d7f9d..be8eeb4a7 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SeedCoordinates.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SeedCoordinates.lean
@@ -247,6 +247,8 @@ theorem pick_iff_place {m : ℕ} (C : DAGCircuit m)
   | inl label =>
     cases j with
     | inl keySlot =>
+      -- Step 1: key summand. The only matching pair is the coordinate `(u, true)` and the single
+      -- key slot.
       cases keySlot
       rw [pick_eq, place_eq]
       change (if label = (u, true) then some (Sum.inl () : ChallengeIndex q) else none) =
@@ -264,6 +266,8 @@ theorem pick_iff_place {m : ℕ} (C : DAGCircuit m)
         · intro h'
           exact (h (Sum.inl.inj (Option.some.inj h')).symm).elim
     | inr nonce =>
+      -- Step 2: mixed summands cannot match. A key label never picks a nonce slot, and `place`
+      -- sends nonce slots only to nonce coordinates.
       rw [pick_eq, place_eq]
       change (if label = (u, true) then some (Sum.inl () : ChallengeIndex q) else none) =
         some (Sum.inr nonce : ChallengeIndex q) ↔
@@ -280,6 +284,8 @@ theorem pick_iff_place {m : ℕ} (C : DAGCircuit m)
   | inr coordinate =>
     cases j with
     | inl keySlot =>
+      -- Step 3: mixed summands cannot match. A nonce coordinate never picks the key slot, and
+      -- `place` sends the key slot to a key label.
       cases keySlot
       rw [pick_eq, place_eq]
       change (NonceCoordinates.pick C rows perm u.val q coordinate).map Sum.inr =
@@ -291,6 +297,8 @@ theorem pick_iff_place {m : ℕ} (C : DAGCircuit m)
         cases heq
       · intro h; cases h
     | inr nonce =>
+      -- Step 4: nonce summand. Injectivity of `Sum.inr` reduces both directions to the
+      -- nonce-coordinate inverse contract `NonceCoordinates.pick_iff_place`.
       rw [pick_eq, place_eq]
       change (NonceCoordinates.pick C rows perm u.val q coordinate).map Sum.inr =
         some (Sum.inr nonce : ChallengeIndex q) ↔
diff --git a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SelectedLaw.lean b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SelectedLaw.lean
index b9ee93390..af99ff49a 100644
--- a/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SelectedLaw.lean
+++ b/TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SelectedLaw.lean
@@ -80,6 +80,8 @@ theorem acceptProb_fill
         X (SelectedSeed.fill C rows (seed (List.ofFn z.1)) u q z.2.1 z.2.2)) D =
       acceptProb (fun r : Fin (10 * S * n + 2 * S) → Bool => X (seed (List.ofFn r))) D := by
   classical
+  -- Step 1: `e` splits the tape into the retained shift/unused-block parameter and the actual
+  -- key/nonce values in their coordinate type; `c` converts the challenge likewise.
   let P := TapeValues.Rest C S n hA hS
   let V := Fin n → Bool
   let e := (TapeValues.equiv C S n hA hS).trans (SeedCoordinates.paramEquiv C V P)
@@ -90,11 +92,13 @@ theorem acceptProb_fill
     Fintype.ofEquiv (V × (Fin (q + 1) → V)) c
   letI : Nonempty (SeedCoordinates.ChallengeIndex q → V) :=
     ⟨c ((fun _ => false), fun _ _ => false)⟩
+  -- Step 2: each parameter's permutations give the matched coordinate exchange `pick`/`place`.
   let perm : P → SeedCoordinates.Permutations C := TapeValues.permutation C S n hA hS
   let pick := fun p : P => SeedCoordinates.pick C rows (perm p) u q
   let place := fun p : P => SeedCoordinates.place C rows (perm p) u q
   have hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i :=
     fun p => SeedCoordinates.pick_iff_place C rows (perm p) u q hargs hcomplete hrows
+  -- Step 3: the seed's inverse reader identifies the original sample with these coordinates.
   have hSeed (z : P × (SeedCoordinates.Index C → V)) :
       seed (List.ofFn (e.symm z)) =
         (SeedCoordinates.seedEquiv C V).symm (perm z.1, z.2) := by
@@ -104,6 +108,7 @@ theorem acceptProb_fill
     rw [SeedCoordinates.paramEquiv_symm,
       TapeValues.seed_on_inverse C S n hA hS seed hK hR₀ hR₁ hP]
     rw [SeedCoordinates.seedEquiv_symm, SeedCoordinates.dataEquiv_symm]
+  -- Step 4: the filled-seed reader identifies the replacement with the matched exchange.
   have hFilled (z : P × (SeedCoordinates.Index C → V))
       (t : SeedCoordinates.ChallengeIndex q → V) :
       SelectedSeed.fill C rows (seed (List.ofFn (e.symm z))) u q
@@ -124,6 +129,7 @@ theorem acceptProb_fill
       Equiv.apply_symm_apply c t
     rw [Equiv.apply_symm_apply, SeedCoordinates.seedEquiv_fill, hp, hd, hc,
       CoordinateSwap.swap_eq]
+  -- Step 5: transport the actual sampler through the tape equivalence `e`.
   let Z := fun z : P × (SeedCoordinates.Index C → V) =>
     X ((SeedCoordinates.seedEquiv C V).symm (perm z.1, z.2))
   have hStart : acceptProb Z D =
@@ -135,6 +141,7 @@ theorem acceptProb_fill
       funext fun z => congrArg X (hSeed z)
     rw [hf] at h
     exact h
+  -- Step 6: pointwise, the filled sampler is the exchanged one under `e.prodCongr c`.
   have hPoint (z : (Fin (10 * S * n + 2 * S) → Bool) ×
       (V × (Fin (q + 1) → V))) :
       X (SelectedSeed.fill C rows (seed (List.ofFn z.1)) u q z.2.1 z.2.2) =
@@ -146,6 +153,8 @@ theorem acceptProb_fill
         (perm (CoordinateSwap.swap pick place (e z.1, c z.2)).1.1,
           (CoordinateSwap.swap pick place (e z.1, c z.2)).1.2))
     exact h
+  -- Step 7: transport through `e.prodCongr c`, apply the exchange's proved uniform acceptance
+  -- law `CoordinateSwap.acceptProb_swap`, and return to the actual tape by Step 5.
   have hTransport := acceptProb_comp_equiv (e.prodCongr c)
     (fun z : (P × (SeedCoordinates.Index C → V)) ×
         (SeedCoordinates.ChallengeIndex q → V) => Z (CoordinateSwap.swap pick place z).1) D

## ===== TCSlib/Cryptography/SecureComputation/Yao.lean (Lean, at 355a0288d56290e8c984228cbc1824187029e456) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Hybrid
import TCSlib.Cryptography.SecureComputation.GarblingSecurity
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Cryptography.Foundations.BitLists
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Yao's protocol in the OT-hybrid model

[PS10, Protocol 162.6]: Alice garbles a circuit for `f` and sends it with the keys of her input
bits; for each of Bob's input bits the parties run an oblivious transfer in which Bob obtains the
key of his bit; Bob evaluates the garbled circuit, sends the result to Alice, and both output it.
[PS10, Theorem 163.7]: the protocol is honest-but-curious secure. By the ruling of 2026-11-05,
both are stated here in the OT-hybrid model of [Gol04, §7.3] (`HybridProtocol otFunctionality`,
`Hybrid.lean`); the real protocol follows by composition with Protocol 160.4, which is not in
this file.

**The circuits** (`YaoCircuit`). The source garbles "a canonical circuit representation of `f`".
Here that is a uniform family of fan-in-two circuits `C_n` (`DAGCircuit`) of polynomial size, on
`inA(n) + inB(n)` inputs, with a list of `outLen(n)` output vertices. Alice's input bits are
vertices `0, …, inA − 1`, Bob's are vertices `inA, …, inA + inB − 1`. Uniformity (a
polynomial-time map from `1^n` to the description `encodeCircuit`) is what lets Alice, Bob and
the simulators build the circuit in polynomial time. The functionality gives both parties the
values of `C_n(x, y)` at the output vertices (`yaoFunctionality`).

**The garbling** is Construction 158.a of `Garbling.lean` with nested special encryption
(`GarblingSpecial.lean`), keys of `n` bits, and the randomness read from fixed blocks of Alice's
coins (`yaoSeed`): the keys, `2n` coins per row, and a shift `λ_i` per gate.

**The protocol** (`yaoHybrid`). `inB(n) · n` ideal bit-OTs, then two messages:
- call `(i, t)` gives Bob bit `t` of the key of his wire `inA + i` for his bit `y_i`;
- Alice sends the garbled tables, the keys of her input bits, and the key pair `(k⁰, k¹)` of every
  output vertex;
- Bob evaluates the garbled circuit with `runWith` and `evalGate`, decodes each output key by
  comparison with its pair, and sends the bits; under D8 the last mover's message is its output,
  and Alice outputs the message she received.

**Deviations from [PS10].**
- **The OT-hybrid model** (ruling of 2026-11-05), with the ideal calls first (`Hybrid.lean`). The
  source's proof simulates the OT transcripts with Proposition 161.5's simulators; here a party's
  view holds its OT outputs instead, and the composition theorem supplies the rest.
- **Bit OTs.** `otFunctionality` transfers one bit, so the source's OT of a key pair `(k_{i,0},
  k_{i,1})` is `n` bit OTs with the same choice bit `y_i` (the source: "it is straightforward to
  generalize this construction to handle `n`-bit values").
- **The row order: a random XOR shift.** Row `a` of gate `i` sits at the position of `a ⊕ λ_i`
  in a fixed enumeration of the assignments, for a uniform `λ_i` (`xorShift`). The source shuffles
  each table uniformly, but the `24` orders of four rows cannot be sampled exactly from a fixed
  number of coin bits. A uniform shift makes the position of the row that opens uniform and
  independent of the inputs, which is what the simulation uses (the point-and-permute idea of
  [BMR90]).
- **Output decoding.** The source does not say how Bob reads the output from the output keys.
  Here Alice sends each output vertex's key pair, and Bob maps `k⁰ ↦ 0`, `k¹ ↦ 1` (`decodeOut`).
- **Output vertices are sinks** (`YaoCircuit.outs_sink`). The decoding pairs reveal both keys of
  every output vertex, so if a gate read an output vertex `o`, Bob could open its table on both
  values of `o`. For `f(x) = (x₀, x₀ ∧ x₁)` with output vertices `x₀` and `g = x₀ ∧ x₁`, Bob
  holds both keys of `x₀`, opens the row `(1, x₁)` of `g`, and decodes `x₁` even when `x₀ = 0`.
  One identity gate per output brings any circuit to this form.
- **Lengths.** Inputs and outputs have polynomial lengths `inA(n)`, `inB(n)`, `outLen(n)` (the
  source: `x, y ∈ {0,1}^n`); the security parameter `n` is the key length.
- **Correctness** needs, besides a good garbling, distinct keys on each output vertex
  (`yaoHybrid_correct`); both hold except with negligible probability (`yaoSeed_good_whp`).
- **A joint PRF.** The two encryption layers use two PRFs `G₁`, `G₂` (`GarblingSpecial.lean`), and
  a wire's key can key both. The security theorem assumes the pair is pseudorandom under one key
  (`yaoHybrid_simulators`); the source uses one scheme for both layers.

## Main definitions

* `SecureComputation.encodeCircuit`: the description of a circuit with an output list.
* `SecureComputation.YaoCircuit`, `YaoCircuit.output`, `yaoFunctionality`: the circuit family and
  the functionality it computes.
* `SecureComputation.readBits`, `assignIdx`, `xorShift`, `yaoCoins`, `yaoSeed`: the garbling's
  randomness from Alice's coins.
* `SecureComputation.decodeMsgs`: the inverse of `Strategy.encodeMsgs`.
* `SecureComputation.yaoTables`, `yaoKeysA`, `yaoPairs`, `yaoMsg`: Alice's message.
* `SecureComputation.yaoBobTables`, `yaoBobInit`, `yaoBobValues`, `decodeOut`, `yaoBobOut`: Bob's
  evaluation.
* `SecureComputation.yaoAlice`, `yaoBob`, `yaoMain`, `yaoCall`, `yaoHybrid`: Protocol 162.6 in the
  OT-hybrid model.

## Main results

* `SecureComputation.encodeCircuit_injective`, `decodeMsgs_encodeMsgs` (proved): the encodings.
* `SecureComputation.yaoBobOut_yaoMsg` (proved): Bob's evaluation of a good garbling with distinct
  output keys gives `f(x, y)`.
* `SecureComputation.yaoHybrid_answersB_getD` (proved): Bob's OT answers are his keys.
* `SecureComputation.yaoHybrid_correct` (proved): both parties output `f(x, y)` in the hybrid
  execution when the garbling is good with distinct output keys.
* `SecureComputation.yaoSeed_good_whp` (proved): the garbling is good with distinct output keys
  except with negligible probability.
* `SecureComputation.yaoHybrid_polyTime` (proved): the protocol is efficient.
* `SecureComputation.yaoHybrid_simulators` (proved): the simulators of Theorem 163.7 in the
  OT-hybrid model.
* `SecureComputation.yaoHybrid_hbcSecure` (Theorem 163.7 in the OT-hybrid model, proved from the
  two previous results).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Protocol 162.6 and Theorem 163.7 (book pp. 156–164).
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, §7.3 (oracle-aided protocols and their composition).
* [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*, STOC 1990,
  pp. 503–513 (the point-and-permute row order).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party computation*,
  Journal of Cryptology 22(2), 2009, pp. 161–188 (the simulator with one active key per wire).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography BoolCircuit

/-! ### Circuit descriptions with an output list -/

/-- **The description of a circuit with an output list** [PS10, Protocol 162.6, "a canonical
circuit representation of `f`"]: the pair of the circuit's description `DAGCircuit.encode` (the
number of inputs, the gates and the output vertex, numbers in unary) and the encoded list of the
output vertices in unary, `⟨C, ⟨o₀, ⟨o₁, …⟩⟩⟩`. The gates are encoded by `DAGGate.encode`. -/
def encodeCircuit {m k : ℕ} (C : DAGCircuit m) (outs : Fin k → ℕ) : List Bool :=
  pairEncode C.encode (Strategy.encodeMsgs (List.ofFn fun j => encodeNat (outs j)))

/-- The description of a circuit with an output list is
`⟨encode C, encodeMsgs [encodeNat o₀, …, encodeNat o_{k−1}]⟩`. -/
theorem encodeCircuit_eq {m k : ℕ} (C : DAGCircuit m) (outs : Fin k → ℕ) :
    encodeCircuit C outs =
      pairEncode C.encode (Strategy.encodeMsgs (List.ofFn fun j => encodeNat (outs j))) := rfl

/-- Encoded message lists of equal length are equal only if the lists are. -/
private theorem encodeMsgs_inj : ∀ {l l' : List (List Bool)}, l.length = l'.length →
    Strategy.encodeMsgs l = Strategy.encodeMsgs l' → l = l'
  | [], [], _, _ => rfl
  | a :: l, b :: l', hlen, h => by
    rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons] at h
    have h₁ := congrArg pairFstD h
    have h₂ := congrArg pairSndD h
    rw [pairFstD_pairEncode, pairFstD_pairEncode] at h₁
    rw [pairSndD_pairEncode, pairSndD_pairEncode] at h₂
    rw [h₁, encodeMsgs_inj (by simpa using hlen) h₂]

/-- The unary code is injective (`decodeNat_encodeNat`). -/
private theorem encodeNat_inj {a b : ℕ} (h : encodeNat a = encodeNat b) : a = b := by
  have ha := decodeNat_encodeNat a []
  have hb := decodeNat_encodeNat b []
  rw [h, hb] at ha
  exact (Prod.mk.inj (Option.some.inj ha)).1.symm

/-- **The description of a circuit with an output list is injective**: equal descriptions come
from equal circuits and equal output lists (`DAGCircuit.encode_injective`, the injectivity of the
pairing and of the unary code). -/
theorem encodeCircuit_injective {m k : ℕ} {C C' : DAGCircuit m} {outs outs' : Fin k → ℕ}
    (h : encodeCircuit C outs = encodeCircuit C' outs') : C = C' ∧ outs = outs' := by
  have h₁ := congrArg pairFstD h
  have h₂ := congrArg pairSndD h
  rw [encodeCircuit_eq, encodeCircuit_eq, pairFstD_pairEncode, pairFstD_pairEncode] at h₁
  rw [encodeCircuit_eq, encodeCircuit_eq, pairSndD_pairEncode, pairSndD_pairEncode] at h₂
  refine ⟨DAGCircuit.encode_injective m h₁, funext fun j => encodeNat_inj ?_⟩
  have h₃ := List.ofFn_injective (encodeMsgs_inj (by simp) h₂)
  exact congrFun h₃ j

/-! ### Uniform circuit families with output lists -/

/-- **A uniform circuit family for Yao's protocol** [PS10, Protocol 162.6, "a canonical circuit
representation of `f`"; §6.2.1, fan-in two]: for each `n`, a fan-in-two circuit `C_n` on
`inA(n) + inB(n)` inputs (Alice's input bits first, then Bob's) with `outLen(n)` output vertices,
none of them read by a gate, of size at most `sizeBound(n)`; and a polynomial-time map sends `1^n`
to the description of `C_n` with its output list. The circuit's own `output` field is not used.

**Deviations.** The output vertices must be sinks (see the module docstring: the decoding pairs
reveal both keys of an output vertex). Uniformity makes the parties efficient; the source fixes a
circuit for `f` without discussing how it is computed. -/
structure YaoCircuit where
  /-- Alice's input length. -/
  inA : PolyExpr
  /-- Bob's input length. -/
  inB : PolyExpr
  /-- The output length. -/
  outLen : PolyExpr
  /-- A polynomial bound on the circuits' sizes. -/
  sizeBound : PolyExpr
  /-- The circuit at parameter `n`: Alice's inputs are vertices `0, …, inA − 1`, Bob's follow. -/
  circ : ∀ n, DAGCircuit (inA.eval n + inB.eval n)
  /-- The output vertices at parameter `n`. -/
  outs : ∀ n, Fin (outLen.eval n) → ℕ
  /-- The output vertices are vertices of the circuit. -/
  outs_lt : ∀ n j, outs n j < (circ n).size
  /-- No gate reads an output vertex. -/
  outs_sink : ∀ n j, ∀ g ∈ (circ n).gates, outs n j ∉ g.args
  /-- The circuits have fan-in two (and are well formed). -/
  fanin : ∀ n, (circ n).IsFaninTwo
  /-- The circuits have polynomial size. -/
  size_le : ∀ n, (circ n).size ≤ sizeBound.eval n
  /-- The family is uniform: a polynomial-time map sends `1^n` to the description of `C_n`. -/
  uniform : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n, E (List.replicate n true) = encodeCircuit (circ n) (outs n)

namespace YaoCircuit

variable (Y : YaoCircuit)

/-- **The function computed by the family**: on Alice's input `x` and Bob's input `y`, bit `j` is
the value of `C_n(x, y)` at the output vertex `o_j`. -/
def output (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) :
    Fin (Y.outLen.eval n) → Bool :=
  fun j => ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false

/-- Bit `j` of the output is the value of `C_n(x, y)` at the output vertex `o_j`. -/
theorem output_apply (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool)
    (j : Fin (Y.outLen.eval n)) :
    Y.output n x y j = ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false := rfl

end YaoCircuit

/-- **The functionality of a Yao circuit family** [PS10, Protocol 162.6, "A and B output the
result `f(x, y)`"]: Alice's input has `inA(n)` bits, Bob's `inB(n)`, and both parties receive the
`outLen(n)` bits `C_n(x, y)` at the output vertices. Its field equations are
`yaoFunctionality_inA`, …, `yaoFunctionality_f`. -/
def yaoFunctionality (Y : YaoCircuit) : Functionality where
  inA := Y.inA
  inB := Y.inB
  outA := Y.outLen
  outB := Y.outLen
  f n x y := (Y.output n x y, Y.output n x y)

attribute [simps (config := { isSimp := false }) inA inB outA outB f] yaoFunctionality

/-! ### The garbling from Alice's coins -/

/-- **`len` bits of a string from position `off`**: bit `t` is the string's bit `off + t`, or
`false` past its end. -/
def readBits (w : List Bool) (off len : ℕ) : Fin len → Bool := fun t => w.getD (off + t) false

/-- Bit `t` of `readBits w off len` is bit `off + t` of `w` (`false` past its end). -/
theorem readBits_apply (w : List Bool) (off len : ℕ) (t : Fin len) :
    readBits w off len t = w.getD (off + t) false := rfl

/-- **The index of an assignment**: the assignment `a` of `len` positions read as a binary number,
position `0` the least significant bit, `Σ_t a_t · 2^t`. It is below `4` for at most two
positions. -/
def assignIdx {len : ℕ} (a : Fin len → Bool) : ℕ :=
  (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0

/-- The index of an assignment is the fold `b₀ + 2 (b₁ + 2 (⋯))` of its bits. -/
theorem assignIdx_eq {len : ℕ} (a : Fin len → Bool) :
    assignIdx a = (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 := rfl

/-- **The XOR shift by `λ`**: the permutation `a ↦ a ⊕ λ` of the assignments of `len` positions,
an involution. It is the row order of the garbled tables ([BMR90]'s point-and-permute; declared
deviation from [PS10, §6.2.3]'s uniform shuffle, see the module docstring). -/
def xorShift {len : ℕ} (l : Fin len → Bool) : Equiv.Perm (Fin len → Bool) :=
  Function.Involutive.toPerm (fun a p => xor (a p) (l p)) fun a => funext fun p => by
    show xor (xor (a p) (l p)) (l p) = a p
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The XOR shift by `λ` maps `a` to `a ⊕ λ`, position by position. -/
theorem xorShift_apply {len : ℕ} (l a : Fin len → Bool) :
    xorShift l a = fun p => xor (a p) (l p) := rfl

/-- The inverse XOR shift is the same pointwise XOR operation. -/
theorem xorShift_symm_apply {len : ℕ} (l a : Fin len → Bool) :
    (xorShift l).symm a = fun p => xor (a p) (l p) := rfl

/-- **Alice's number of coins**: `10 · S(n) · n + 2 · S(n)` for the size bound `S`; `2 · S(n) · n`
for the keys, `8 · S(n) · n` for the row coins (at most four rows of `2n` coins per gate), and
`2 · S(n)` for the shifts. -/
def yaoCoins (Y : YaoCircuit) : PolyExpr :=
  .add (.mul (.mul (.const 10) Y.sizeBound) .var) (.mul (.const 2) Y.sizeBound)

/-- Alice's coin-count expression is `10 S(n)n + 2 S(n)` syntactically. -/
theorem yaoCoins_eq (Y : YaoCircuit) :
    yaoCoins Y = .add (.mul (.mul (.const 10) Y.sizeBound) .var)
      (.mul (.const 2) Y.sizeBound) := rfl

/-- Alice has `10 · S(n) · n + 2 · S(n)` coins. -/
theorem yaoCoins_eval (Y : YaoCircuit) (n : ℕ) :
    (yaoCoins Y).eval n = 10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n := rfl

/-- **The garbling's randomness from Alice's coins** [PS10, §6.2.2–6.2.3: random key pairs,
encryption coins, shuffled rows], at key length `n`, with `S = sizeBound(n)`:
- the key of vertex `v` for the bit `b`: the `n` coins from `(b · S + v) · n`;
- the coins of row `a` of gate `i`: the `2n` coins from `2 S n + (4 i + idx(a)) · 2n`, split in
  halves (the outer and inner layer's coins);
- the row order of gate `i`: the XOR shift by the coins from `10 S n + 2 i`.

For a fan-in-two circuit of size at most `S` these blocks are disjoint, so uniform coins give
independent uniform keys and row coins, and uniform shifts.

**Deviation.** The row order is a uniform XOR shift, not a uniform permutation (module docstring).
-/
def yaoSeed (Y : YaoCircuit) (n : ℕ) (r : List Bool) :
    GarbleSeed (Y.circ n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) :=
  (fun v b => readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n,
    fun i a => (readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n)) n,
      readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n) + n) n),
    fun i => xorShift (readBits r (10 * Y.sizeBound.eval n * n + 2 * i) _))

/-- The key of vertex `v` for the bit `b` is the `n` coins from `(b · S + v) · n`. -/
theorem yaoSeed_fst (Y : YaoCircuit) (n : ℕ) (r : List Bool) (v : Fin (Y.circ n).size)
    (b : Bool) :
    (yaoSeed Y n r).1 v b = readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n := rfl

/-- The coins of row `a` of gate `i` are the two `n`-bit halves of the `2n` coins from
`2 S n + (4 i + idx(a)) · 2n`. -/
theorem yaoSeed_snd_fst (Y : YaoCircuit) (n : ℕ) (r : List Bool)
    (i : Fin (Y.circ n).gates.length) (a : Fin ((Y.circ n).gates[i]).args.length → Bool) :
    (yaoSeed Y n r).2.1 i a =
      (readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n)) n,
        readBits r (2 * Y.sizeBound.eval n * n + (4 * i + assignIdx a) * (2 * n) + n) n) := rfl

/-- The row order of gate `i` is the XOR shift by the coins from `10 S n + 2 i`. -/
theorem yaoSeed_snd_snd (Y : YaoCircuit) (n : ℕ) (r : List Bool)
    (i : Fin (Y.circ n).gates.length) :
    (yaoSeed Y n r).2.2 i = xorShift (readBits r (10 * Y.sizeBound.eval n * n + 2 * i) _) := rfl

/-- The key of a vertex `v` of the circuit for the bit `b` is the `n` coins from
`(b · S + v) · n`. -/
theorem keyAt_yaoSeed (Y : YaoCircuit) (n : ℕ) (r : List Bool) {v : ℕ}
    (hv : v < (Y.circ n).size) (b : Bool) :
    keyAt (Y.circ n) (yaoSeed Y n r) v b =
      readBits r ((b.toNat * Y.sizeBound.eval n + v) * n) n := by
  rw [keyAt_eq, dif_pos hv, yaoSeed_fst]

/-! ### Message lists -/

/-- **Decoding a message list**, the inverse of `Strategy.encodeMsgs`: the first component of the
string, then the decoding of the second, until the empty string (at most `|w|` components).
Delegates to the public word-list decoder, including on malformed words. -/
def decodeMsgs (w : List Bool) : List (List Bool) := BinArith.decWords w

/-- Decoding any word gives `[]` when the word is empty, and otherwise its first pair
component followed by the decoding of its second component, including on malformed words.

**Proof sketch.** Apply the public empty or nonempty equation of `BinArith.decWords`, according
to whether the input word is empty. -/
theorem decodeMsgs_eq (w : List Bool) :
    decodeMsgs w = if w = [] then [] else pairFstD w :: decodeMsgs (pairSndD w) :=
  if hw : w = [] then
    (congrArg decodeMsgs hw).trans (BinArith.decWords_nil.trans (if_pos hw).symm)
  else
    (BinArith.decWords_of_ne hw).trans (if_neg hw).symm

/-- **Decoding inverts the message-list encoding**: `decodeMsgs (encodeMsgs l) = l`.

**Proof sketch.** The public nil and cons equations identify `Strategy.encodeMsgs` with
`BinArith.encWords` by list recursion. Apply `BinArith.decWords_encWords`. -/
theorem decodeMsgs_encodeMsgs (l : List (List Bool)) :
    decodeMsgs (Strategy.encodeMsgs l) = l := by
  have henc : ∀ ms : List (List Bool), Strategy.encodeMsgs ms = BinArith.encWords ms :=
    List.rec (motive := fun ms : List (List Bool) =>
      Strategy.encodeMsgs ms = BinArith.encWords ms)
      (Strategy.encodeMsgs_nil.trans BinArith.encWords_nil.symm)
      (fun m ms ih => (Strategy.encodeMsgs_cons m ms).trans
        ((congrArg (pairEncode m) ih).trans (BinArith.encWords_cons m ms).symm))
  exact (congrArg BinArith.decWords (henc l)).trans (BinArith.decWords_encWords l)

/-- The empty string decodes to the empty list. -/
theorem decodeMsgs_nil : decodeMsgs [] = [] := BinArith.decWords_nil

/-! ### Alice's message -/

variable (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)

/-- **The garbled tables** [PS10, Protocol 162.6, "A generates a garbled circuit … and sends the
circuit"]: gate by gate, the garbled table of `yaoSeed` with nested special encryption, each
table an encoded list of rows, and the tables an encoded list. -/
noncomputable def yaoTables (n : ℕ) (r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun i : Fin (Y.circ n).gates.length =>
    Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) i))

/-- The garbled tables are the encoded list of the encoded garbled tables. -/
theorem yaoTables_eq (n : ℕ) (r : List Bool) :
    yaoTables Y E₁ E₂ n r = Strategy.encodeMsgs (List.ofFn fun i : Fin (Y.circ n).gates.length =>
      Strategy.encodeMsgs (garbledTable (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) i)) :=
  rfl

/-- **Alice's input keys** [PS10, Protocol 162.6, "the input keys corresponding to the bits of
`x`"]: the encoded list of the keys `k_v^{x_v}` of her input vertices `v < inA(n)`, for her
input `xs`. -/
def yaoKeysA (n : ℕ) (xs r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun v : Fin (Y.inA.eval n) =>
    List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) v (xs.getD v false)))

/-- Alice's input keys are the encoded list of `k_v^{x_v}` for `v < inA(n)`. -/
theorem yaoKeysA_eq (n : ℕ) (xs r : List Bool) :
    yaoKeysA Y n xs r = Strategy.encodeMsgs (List.ofFn fun v : Fin (Y.inA.eval n) =>
      List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) v (xs.getD v false))) := rfl

/-- **The decoding pairs**: for each output index `j`, the pair `⟨k_{o_j}^0, k_{o_j}^1⟩` of the
keys of the output vertex `o_j`, as an encoded list.

**Deviation.** Not in [PS10], which does not say how Bob reads the output (module docstring). -/
def yaoPairs (n : ℕ) (r : List Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun j : Fin (Y.outLen.eval n) =>
    pairEncode (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false))
      (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true)))

/-- The decoding pairs are the encoded list of `⟨k_{o_j}^0, k_{o_j}^1⟩`. -/
theorem yaoPairs_eq (n : ℕ) (r : List Bool) :
    yaoPairs Y n r = Strategy.encodeMsgs (List.ofFn fun j : Fin (Y.outLen.eval n) =>
      pairEncode (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false))
        (List.ofFn (keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true))) := rfl

/-- **Alice's message** [PS10, Protocol 162.6, first step]: `⟨tables, ⟨her input keys, decoding
pairs⟩⟩`, for her input `xs` and her coins `r`. -/
noncomputable def yaoMsg (n : ℕ) (xs r : List Bool) : List Bool :=
  pairEncode (yaoTables Y E₁ E₂ n r) (pairEncode (yaoKeysA Y n xs r) (yaoPairs Y n r))

/-- Alice's message is `⟨tables, ⟨input keys, decoding pairs⟩⟩`. -/
theorem yaoMsg_eq (n : ℕ) (xs r : List Bool) :
    yaoMsg Y E₁ E₂ n xs r =
      pairEncode (yaoTables Y E₁ E₂ n r) (pairEncode (yaoKeysA Y n xs r) (yaoPairs Y n r)) := rfl

/-! ### Bob's evaluation -/

/-- **The tables Bob reads**: at a gate vertex `v ≥ inA + inB`, the decoded list of rows of the
`(v − inA − inB)`-th encoded table of the message; none at an input vertex. -/
def yaoBobTables (n : ℕ) (msg : List Bool) (v : ℕ) : List (List Bool) :=
  if Y.inA.eval n + Y.inB.eval n ≤ v then
    decodeMsgs ((decodeMsgs (pairFstD msg)).getD (v - (Y.inA.eval n + Y.inB.eval n)) [])
  else []

/-- Bob's table at `v` is the decoded `(v − inA − inB)`-th table at a gate vertex, and empty at
an input vertex. -/
theorem yaoBobTables_eq (n : ℕ) (msg : List Bool) (v : ℕ) :
    yaoBobTables Y n msg v = if Y.inA.eval n + Y.inB.eval n ≤ v then
      decodeMsgs ((decodeMsgs (pairFstD msg)).getD (v - (Y.inA.eval n + Y.inB.eval n)) [])
    else [] := rfl

/-- **Bob's input keys** [PS10, Protocol 162.6, "using the keys for all input wires"]: at Alice's
vertex `v < inA(n)`, the `v`-th key of the message; at his vertex `inA(n) + i`, bits `i · n` to
`i · n + n − 1` of his OT answers `ans`. -/
def yaoBobInit (n : ℕ) (msg ans : List Bool) : List (Fin n → Bool) :=
  List.ofFn fun v : Fin (Y.inA.eval n + Y.inB.eval n) =>
    if (v : ℕ) < Y.inA.eval n then padFin n ((decodeMsgs (pairFstD (pairSndD msg))).getD v [])
    else readBits ans (((v : ℕ) - Y.inA.eval n) * n) n

/-- Bob's input keys: Alice's `v`-th key from the message at `v < inA`, his answer bits from
`(v − inA) · n` otherwise. -/
theorem yaoBobInit_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobInit Y n msg ans = List.ofFn fun v : Fin (Y.inA.eval n + Y.inB.eval n) =>
      if (v : ℕ) < Y.inA.eval n then padFin n ((decodeMsgs (pairFstD (pairSndD msg))).getD v [])
      else readBits ans (((v : ℕ) - Y.inA.eval n) * n) n := rfl

/-- **Bob's garbled evaluation** [PS10, Protocol 162.6, "B evaluates the circuit"; §6.2.3, "attempt
to decrypt all four rows"]: `runWith` over the gates of `C_n` from his input keys, each gate opened
by `evalGate` on the table he read at its vertex. -/
def yaoBobValues (n : ℕ) (msg ans : List Bool) : List (Fin n → Bool) :=
  runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ n) (yaoBobTables Y n msg) vs.length g vs)
    (Y.circ n).gates (yaoBobInit Y n msg ans)

/-- Bob's garbled evaluation is `runWith` of `evalGate` on his tables from his input keys. -/
theorem yaoBobValues_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobValues Y E₁ E₂ n msg ans =
      runWith (fun g vs => evalGate (nestedSpecial E₁ E₂ n) (yaoBobTables Y n msg) vs.length g vs)
        (Y.circ n).gates (yaoBobInit Y n msg ans) := rfl

/-- **Decoding an output key** by its pair `p = ⟨k⁰, k¹⟩`: `k⁰ ↦ false`, `k¹ ↦ true`, anything
else `↦ false`.

**Deviation.** Not in [PS10] (module docstring). -/
def decodeOut (k p : List Bool) : Bool :=
  if k = pairFstD p then false else decide (k = pairSndD p)

/-- Decoding an output key: `false` if it is the first key of the pair, otherwise whether it is
the second. -/
theorem decodeOut_eq (k p : List Bool) :
    decodeOut k p = if k = pairFstD p then false else decide (k = pairSndD p) := rfl

/-- The first key of a pair decodes to `false`. -/
theorem decodeOut_fst (k₀ k₁ : List Bool) : decodeOut k₀ (pairEncode k₀ k₁) = false := by
  rw [decodeOut, pairFstD_pairEncode, if_pos rfl]

/-- The second key of a pair of distinct keys decodes to `true`. -/
theorem decodeOut_snd (k₀ k₁ : List Bool) (h : k₁ ≠ k₀) :
    decodeOut k₁ (pairEncode k₀ k₁) = true := by
  rw [decodeOut, pairFstD_pairEncode, pairSndD_pairEncode, if_neg h, decide_eq_true rfl]

/-- **Bob's result** [PS10, Protocol 162.6, last step]: for each output index `j`, the key his
evaluation reaches at the output vertex `o_j`, decoded by the `j`-th pair of the message. -/
def yaoBobOut (n : ℕ) (msg ans : List Bool) : List Bool :=
  List.ofFn fun j : Fin (Y.outLen.eval n) =>
    decodeOut (List.ofFn ((yaoBobValues Y E₁ E₂ n msg ans).getD (Y.outs n j) default))
      ((decodeMsgs (pairSndD (pairSndD msg))).getD j [])

/-- Bob's result: bit `j` decodes the key at `o_j` by the `j`-th decoding pair. -/
theorem yaoBobOut_eq (n : ℕ) (msg ans : List Bool) :
    yaoBobOut Y E₁ E₂ n msg ans = List.ofFn fun j : Fin (Y.outLen.eval n) =>
      decodeOut (List.ofFn ((yaoBobValues Y E₁ E₂ n msg ans).getD (Y.outs n j) default))
        ((decodeMsgs (pairSndD (pairSndD msg))).getD j []) := rfl

/-! ### The protocol -/

/-- **Alice in Protocol 162.6** [PS10] (the prover's role, `Defs.lean`'s convention), on common
input `1^n`, private input `⟨x, answers⟩` (her answers are empty: OT gives the sender `⊥`) and
coins `r`: on the empty history, her message `yaoMsg`; on a nonempty history, its first message,
which is her output ("A and B output the result"). Her coins are `yaoCoins`. -/
noncomputable def yaoAlice : Strategy where
  next x z r hist := match hist with
    | [] => yaoMsg Y E₁ E₂ x.length (pairFstD z) r
    | m :: _ => m
  coins := yaoCoins Y

/-- On the empty history Alice sends `yaoMsg` at `|x|` for her input `pairFstD z`. -/
theorem yaoAlice_next_nil (x z r : List Bool) :
    (yaoAlice Y E₁ E₂).next x z r [] = yaoMsg Y E₁ E₂ x.length (pairFstD z) r := rfl

/-- On a nonempty history Alice returns its first message. -/
theorem yaoAlice_next_cons (x z r m : List Bool) (hist : List (List Bool)) :
    (yaoAlice Y E₁ E₂).next x z r (m :: hist) = m := rfl

/-- Alice's coin polynomial is `yaoCoins`. -/
theorem yaoAlice_coins : (yaoAlice Y E₁ E₂).coins = yaoCoins Y := rfl

/-- **Bob in Protocol 162.6** [PS10] (the verifier's role), on common input `1^n` and private
input `⟨y, answers⟩`: his result `yaoBobOut` on the first message received and his answers. He
moves last, so his message is also his output. He uses no coins. -/
def yaoBob : Strategy where
  next x z _ hist := yaoBobOut Y E₁ E₂ x.length (hist.headD []) (pairSndD z)
  coins := .const 0

/-- Bob's message is `yaoBobOut` at `|x|` on the first message received and his answers. -/
theorem yaoBob_next (x z r : List Bool) (hist : List (List Bool)) :
    (yaoBob Y E₁ E₂).next x z r hist =
      yaoBobOut Y E₁ E₂ x.length (hist.headD []) (pairSndD z) := rfl

/-- Bob uses no coins. -/
theorem yaoBob_coins : (yaoBob Y E₁ E₂).coins = .const 0 := rfl

/-- **The message phase of Protocol 162.6** [PS10]: two messages, Alice first; Alice sends the
garbled circuit and her keys, Bob returns `f(x, y)`. Its fields are `yaoMain_P`, …,
`yaoMain_verifierFirst`. -/
noncomputable def yaoMain : Protocol where
  P := yaoAlice Y E₁ E₂
  V := yaoBob Y E₁ E₂
  rounds := .const 2
  verifierFirst := false

attribute [simps (config := { isSimp := false }) P V rounds verifierFirst] yaoMain

/-- **Bob's output in the message phase**: Bob's result on Alice's message and his answers. -/
theorem yaoMain_outV (w zA zB : List Bool)
    (r : (yaoMain Y E₁ E₂).ExecCoins (yaoMain Y E₁ E₂).P w) :
    (yaoMain Y E₁ E₂).outV (yaoMain Y E₁ E₂).P w zA zB r =
      yaoBobOut Y E₁ E₂ w.length (yaoMsg Y E₁ E₂ w.length (pairFstD zA) (List.ofFn r.1))
        (pairSndD zB) := by
  simp [Protocol.outV_eq, Protocol.transcriptWith_eq, yaoMain_P, yaoMain_V,
    yaoMain_rounds, yaoMain_verifierFirst, PolyExpr.eval_const, exec_succ, exec_zero,
    moverIsV_false, yaoAlice_next_nil, yaoBob_next]

/-- **Alice's output in the message phase**: the message Bob sent, his result. -/
theorem yaoMain_outP (w zA zB : List Bool)
    (r : (yaoMain Y E₁ E₂).ExecCoins (yaoMain Y E₁ E₂).P w) :
    (yaoMain Y E₁ E₂).outP w zA zB r =
      yaoBobOut Y E₁ E₂ w.length (yaoMsg Y E₁ E₂ w.length (pairFstD zA) (List.ofFn r.1))
        (pairSndD zB) := by
  simp [Protocol.outP_eq, Protocol.transcriptWith_eq, yaoMain_P, yaoMain_V,
    yaoMain_rounds, yaoMain_verifierFirst, PolyExpr.eval_const, exec_succ, exec_zero,
    moverIsV_false, yaoAlice_next_nil, yaoAlice_next_cons, yaoBob_next]

/-- **The OT call index**: call `j < inB(n) · n` transfers bit `t` of the keys of Bob's wire
`inA + i`, for `(i, t) = finProdFinEquiv⁻¹ j`, that is `j = i · n + t`. -/
def yaoCall (n : ℕ) (j : Fin (Y.inB.eval n * n)) : Fin (Y.inB.eval n) × Fin n :=
  finProdFinEquiv.symm j

/-- The OT call index is `finProdFinEquiv⁻¹`. -/
theorem yaoCall_eq (n : ℕ) (j : Fin (Y.inB.eval n * n)) :
    yaoCall Y n j = finProdFinEquiv.symm j := rfl

/-- Call `finProdFinEquiv (i, t)` (that is `i · n + t`) has index `(i, t)`. -/
theorem yaoCall_finProdFinEquiv (n : ℕ) (i : Fin (Y.inB.eval n)) (t : Fin n) :
    yaoCall Y n (finProdFinEquiv (i, t)) = (i, t) := by
  rw [yaoCall, Equiv.symm_apply_apply]

/-- **Protocol 162.6 in the OT-hybrid model** [PS10, Protocol 162.6; Gol04, §7.3]: `inB(n) · n`
ideal bit OTs, then `yaoMain`. In call `(i, t)` Alice's input is bit `t` of the two keys of
Bob's wire `inA + i` (from her coins, through `yaoSeed`), Bob's is his bit `y_i`. Its fields are
`yaoHybrid_main`, `yaoHybrid_calls`, `yaoHybrid_callA`, `yaoHybrid_callB`.

**Deviation.** The source's OT of a key pair is `n` bit OTs with the same choice bit (module
docstring). -/
noncomputable def yaoHybrid : HybridProtocol otFunctionality where
  main := yaoMain Y E₁ E₂
  calls := .mul Y.inB .var
  callA n _ r j c := keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + (yaoCall Y n j).1)
    (decide ((c : ℕ) = 1)) (yaoCall Y n j).2
  callB n y _ j _ := y.getD (yaoCall Y n j).1 false

attribute [simps (config := { isSimp := false }) main calls] yaoHybrid

/-- Alice's input to call `j = (i, t)` is `c ↦ k_{inA + i}^{c = 1}[t]`. -/
theorem yaoHybrid_callA (n : ℕ) (xs r : List Bool) (j : Fin (Y.inB.eval n * n)) (c : Fin 2) :
    (yaoHybrid Y E₁ E₂).callA n xs r j
        (Fin.cast ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_inA).trans
          (PolyExpr.eval_const 2 n)).symm c) =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + (yaoCall Y n j).1) (decide ((c : ℕ) = 1))
        (yaoCall Y n j).2 := rfl

/-- Bob's input to call `j = (i, t)` is his bit `y_i`. -/
theorem yaoHybrid_callB (n : ℕ) (ys r : List Bool) (j : Fin (Y.inB.eval n * n)) (c : Fin 1) :
    (yaoHybrid Y E₁ E₂).callB n ys r j
        (Fin.cast ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_inB).trans
          (PolyExpr.eval_const 1 n)).symm c) = ys.getD (yaoCall Y n j).1 false := rfl

/-! ### Correctness -/

/-- Reading a list of a function at an index of the function's domain. -/
private theorem getD_ofFn' {α : Type} {k : ℕ} (f : Fin k → α) (i : Fin k) (d : α) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- **Bob reads the garbled tables**: on Alice's message, the tables Bob reads are the garbled
tables `tableAt` of her garbling, at every vertex. -/
theorem yaoBobTables_yaoMsg (n : ℕ) (xs r : List Bool) :
    yaoBobTables Y n (yaoMsg Y E₁ E₂ n xs r) =
      tableAt (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r) := by
  funext v
  rw [tableAt_eq, yaoBobTables_eq, yaoMsg_eq, yaoTables_eq, pairFstD_pairEncode,
    decodeMsgs_encodeMsgs]
  by_cases h1 : Y.inA.eval n + Y.inB.eval n ≤ v
  · rw [if_pos h1]
    by_cases h2 : v - (Y.inA.eval n + Y.inB.eval n) < (Y.circ n).gates.length
    · rw [dif_pos ⟨h1, h2⟩, List.getD_eq_getElem _ _ (by simpa using h2), List.getElem_ofFn,
        decodeMsgs_encodeMsgs]
    · rw [dif_neg (fun h => h2 h.2), List.getD_eq_default _ _ (by simp; omega), decodeMsgs_nil]
  · rw [if_neg h1, dif_neg (fun h => h1 h.1)]

/-- **Bob's input keys are the input keys of `(x, y)`**: on Alice's message for `x`, and answers
that hold, at bits `i · n + t`, the bits of the keys `k_{inA + i}^{y_i}`, Bob's input keys are
`inputKeys` of `x ‖ y`.

**Proof sketch.** Vertex by vertex. At Alice's vertex `v < inA`, the second component of the
message decodes to her keys (`decodeMsgs_encodeMsgs`), and its `v`-th entry is `k_v^{x_v}`
(`padFin_ofFn`), with `x_v = (x ‖ y)_v` (`Fin.append_left`). At Bob's vertex `inA + i`, the
answer bits `i · n + t` are the bits of `k_{inA + i}^{y_i}` by hypothesis, with
`y_i = (x ‖ y)_{inA + i}` (`Fin.append_right`). -/
theorem yaoBobInit_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool)
    (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t) :
    yaoBobInit Y n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
      inputKeys (Y.circ n) (yaoSeed Y n r) (Fin.append x y) := by
  rw [inputKeys_eq, yaoBobInit_eq]
  congr 1
  funext v
  rw [yaoMsg_eq, pairSndD_pairEncode, pairFstD_pairEncode, yaoKeysA_eq, decodeMsgs_encodeMsgs]
  by_cases hv : (v : ℕ) < Y.inA.eval n
  · rw [if_pos hv, getD_ofFn' _ ⟨v, hv⟩, padFin_ofFn, getD_ofFn' x ⟨v, hv⟩]
    have hx := Fin.append_left x y ⟨v, hv⟩
    rw [show Fin.castAdd (Y.inB.eval n) ⟨(v : ℕ), hv⟩ = v from Fin.ext rfl] at hx
    rw [hx]
  · rw [if_neg hv]
    have hi : (v : ℕ) - Y.inA.eval n < Y.inB.eval n := by omega
    have hy := Fin.append_right x y ⟨v - Y.inA.eval n, hi⟩
    rw [show Fin.natAdd (Y.inA.eval n) ⟨(v : ℕ) - Y.inA.eval n, hi⟩ = v from
      Fin.ext (by simp; omega)] at hy
    rw [hy]
    funext t
    have hv' : Y.inA.eval n + ((v : ℕ) - Y.inA.eval n) = v := by omega
    rw [readBits_apply, hans ⟨v - Y.inA.eval n, hi⟩ t, Fin.val_mk, hv']

/-- **Bob's evaluation is the garbled evaluation**: on Alice's message and answers holding the
keys of Bob's bits, Bob's values are `garbledValues` of her garbling from the input keys of
`x ‖ y`. -/
theorem yaoBobValues_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t) :
    yaoBobValues Y E₁ E₂ n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans =
      garbledValues (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r)
        (inputKeys (Y.circ n) (yaoSeed Y n r) (Fin.append x y)) := by
  rw [yaoBobValues_eq, yaoBobTables_yaoMsg, yaoBobInit_yaoMsg Y E₁ E₂ n x y r ans hans,
    garbledValues_eq]

/-- **Bob computes `f(x, y)`** [PS10, Protocol 162.6, "B evaluates the circuit to compute the
output `f(x, y)`"; Claim 159.a]: on Alice's message for `x`, with answers holding the keys of
Bob's bits `y`, if the garbling is good and every output vertex has two distinct keys, Bob's
result is `C_n(x, y)` at the output vertices.

**Proof sketch.** Bob's tables are the garbled tables and his input keys those of `x ‖ y`
(`yaoBobTables_yaoMsg`, `yaoBobInit_yaoMsg`), so his evaluation is `garbledValues`
(`yaoBobValues_yaoMsg`). By `garbledValues_getD` it reaches the key `k_o^{v_o}` of each output
vertex `o`'s value. The `j`-th decoding pair is `⟨k_o^0, k_o^1⟩`, and with distinct keys
`decodeOut` returns `v_o` (`decodeOut_fst`, `decodeOut_snd`). -/
theorem yaoBobOut_yaoMsg (n : ℕ) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true) :
    yaoBobOut Y E₁ E₂ n (yaoMsg Y E₁ E₂ n (List.ofFn x) r) ans = List.ofFn (Y.output n x y) := by
  rw [yaoBobOut_eq, yaoBobValues_yaoMsg Y E₁ E₂ n x y r ans hans]
  congr 1
  funext j
  rw [garbledValues_getD _ _ _ hgood _ _ (Y.outs_lt n j), yaoMsg_eq, pairSndD_pairEncode,
    pairSndD_pairEncode, yaoPairs_eq, decodeMsgs_encodeMsgs, getD_ofFn', YaoCircuit.output_apply]
  cases ((Y.circ n).values (Fin.append x y)).getD (Y.outs n j) false
  · exact decodeOut_fst _ _
  · exact decodeOut_snd _ _ fun h => hdist j (List.ofFn_injective h).symm

/-- **Bob's OT answers are the keys of his bits**: in the hybrid execution, bit `i · n + t` of
Bob's answers is bit `t` of the key `k_{inA + i}^{y_i}` of his wire `inA + i` for his bit `y_i`
(`otFunctionality_f_snd`). -/
theorem yaoHybrid_answersB_getD (n : ℕ) (xs ys rA rB : List Bool) (i : Fin (Y.inB.eval n))
    (t : Fin n) :
    ((yaoHybrid Y E₁ E₂).answersB n xs ys rA rB).getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n rA) (Y.inA.eval n + i) (ys.getD i false) t := by
  have h := flatten_ofFn_one (k := Y.inB.eval n * n) (l := otFunctionality.outB.eval n)
    ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_outB).trans
      (PolyExpr.eval_const 1 n))
    fun j => (otFunctionality.f n ((yaoHybrid Y E₁ E₂).callA n xs rA j)
      ((yaoHybrid Y E₁ E₂).callB n ys rB j)).2
  have hj : i * n + t = (finProdFinEquiv (i, t) : ℕ) := by
    rw [finProdFinEquiv_apply_val]; ring
  rw [HybridProtocol.answersB_eq]
  -- Normalize the owner-local hybrid call count in the list binder before using `h`.
  change (List.ofFn (fun j : Fin (Y.inB.eval n * n) =>
    List.ofFn ((otFunctionality.f n ((yaoHybrid Y E₁ E₂).callA n xs rA j)
      ((yaoHybrid Y E₁ E₂).callB n ys rB j)).2))).flatten.getD (i * n + t) false = _
  rw [h, hj, getD_ofFn', otFunctionality_f_snd_apply,
    yaoHybrid_callA, yaoHybrid_callB, yaoCall_finProdFinEquiv]
  cases ys.getD i false <;> rfl

/-- `yaoBobOut_yaoMsg` at a parameter `L` equal to `n` (for the common input `1^n`, whose length
is `n` only propositionally). -/
private theorem yaoBobOut_yaoMsg_of_eq {L n : ℕ} (hL : L = n) (x : Fin (Y.inA.eval n) → Bool)
    (y : Fin (Y.inB.eval n) → Bool) (r ans : List Bool)
    (hans : ∀ (i : Fin (Y.inB.eval n)) (t : Fin n), ans.getD (i * n + t) false =
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.inA.eval n + i) (y i) t)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n r))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n r) (Y.outs n j) true) :
    yaoBobOut Y E₁ E₂ L (yaoMsg Y E₁ E₂ L (List.ofFn x) r) ans = List.ofFn (Y.output n x y) := by
  subst hL
  exact yaoBobOut_yaoMsg Y E₁ E₂ L x y r ans hans hgood hdist

/-- **Correctness of Protocol 162.6 in the OT-hybrid model** [PS10, Protocol 162.6, "A and B
output the result `f(x, y)`"; the output clause of Theorem 163.7]: in the hybrid execution with
common input `1^n`, inputs `x`, `y` and coins `r`, if Alice's garbling is good and every output
vertex has two distinct keys, Bob's output and Alice's output are both `f(x, y)`.

**Deviation.** The source needs no hypothesis on the output keys, since it does not say how Bob
decodes them. Equal keys on an output vertex (probability `2^{-n}` each) make the decoding
ambiguous; `yaoSeed_good_whp` bounds both failure events.

**Proof sketch.** Bob's answers hold the keys of his bits (`yaoHybrid_answersB_getD`), and his
private input decodes to them (`HybridProtocol.pairSndD_privB`), Alice's to `x`. The message
phase gives Bob the output `yaoBobOut` on Alice's message (`yaoMain_outV`), which is `f(x, y)`
(`yaoBobOut_yaoMsg`, transported along `|1^n| = n`), and Alice outputs what Bob sent
(`yaoMain_outP`). -/
theorem yaoHybrid_correct (n : ℕ) (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
    (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool) (r : (yaoHybrid Y E₁ E₂).Coins n)
    (hgood : Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r.1)))
    (hdist : ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) true) :
    (yaoHybrid Y E₁ E₂).main.outV (yaoHybrid Y E₁ E₂).main.P (List.replicate n true)
        ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        r = List.ofFn ((yaoFunctionality Y).f n x y).2 ∧
      (yaoHybrid Y E₁ E₂).main.outP (List.replicate n true)
        ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        r = List.ofFn ((yaoFunctionality Y).f n x y).1 := by
  have key := yaoBobOut_yaoMsg_of_eq Y E₁ E₂ (List.length_replicate (n := n) (a := true)) x y
    (List.ofFn r.1)
    ((yaoHybrid Y E₁ E₂).answersB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
    (fun i t => by rw [yaoHybrid_answersB_getD, getD_ofFn']) hgood hdist
  refine ⟨?_, ?_⟩
  · show (yaoMain Y E₁ E₂).outV (yaoMain Y E₁ E₂).P (List.replicate n true) _ _ r = _
    rw [yaoMain_outV, HybridProtocol.pairFstD_privA, HybridProtocol.pairSndD_privB]
    exact key
  · show (yaoMain Y E₁ E₂).outP (List.replicate n true) _ _ r = _
    rw [yaoMain_outP, HybridProtocol.pairFstD_privA, HybridProtocol.pairSndD_privB]
    exact key

/-! ### Theorem 163.7 in the OT-hybrid model -/

section Security

variable (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hGE₁ hGE₂ in
/-- **Alice's garbling is good, with distinct output keys, with high probability** [PS10, §6.2.3,
"all but one row will evaluate to `⊥`" (Claim 159.a)]: with nested special encryption from two
PRFs `G₁`, `G₂` evaluated by `E₁`, `E₂`, there is a negligible `δ` such that for every `n`, on
uniform coins for Alice, the garbling `yaoSeed` fails to be good, or gives some output vertex two
equal keys, with probability at most `δ(n)`.

**Proof sketch.** Write `S = sizeBound(n)`. Distinct blocks contain all vertex keys and
row coins: vertices and gates are below `S`, and binary assignment indices are injective
below four for fan-in at most two. The generic block restriction theorem gives their joint
uniform law, including zero-length blocks. Apply the strengthened B2 uniform-data bound
with `nestedSpecial_wrongKeyBot` and correctness; this bound permits arbitrary seed-dependent
row permutations, including the XOR shifts. Each output's two keys coincide with probability
`2^{-n}`. The output union bound allows repeated vertices. Thus failure is at most
`12*S(n)*δ₀(n) + outLen(n)*2^{-n}`, a sum of polynomial multiples of negligible functions. -/
theorem yaoSeed_good_whp (hG₁ : PRFOut (.add .var .var) G₁)
    (hG₂ : PRFOut (.add .var innerLen) G₂) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ n, uprob (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
      ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
        ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
          keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)) ≤ δ n := by
  classical
  obtain ⟨δ₀, hδ₀, hbot⟩ :=
    nestedSpecial_wrongKeyBot G₁ G₂ E₁ E₂ hGE₁ hGE₂ hG₁ hG₂
  refine ⟨fun n => 12 * (Y.sizeBound.eval n : ℝ) * δ₀ n +
    (Y.outLen.eval n : ℝ) * (2 : ℝ)⁻¹ ^ n, ?_, fun n => ?_⟩
  · simpa only [PolyExpr.eval_mul, PolyExpr.eval_const, Nat.cast_mul, Nat.cast_ofNat] using
      (EnsembleLemmas.negligible_polyExpr_mul (.mul (.const 12) Y.sizeBound) hδ₀).add
        (EnsembleLemmas.negligible_polyExpr_mul Y.outLen negligible_two_pow_neg)
  · have hg : (Y.circ n).gates.length ≤ Y.sizeBound.eval n := by
      have hs := Y.size_le n
      rw [DAGCircuit.size_eq] at hs
      omega
    have hsmall (i : Fin (Y.circ n).gates.length) :=
      GarblingProbability.assignmentFold_small ((Y.circ n).gates[i]).args.length
        (((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _
          (List.getElem_mem i.isLt))
    have hlaw : HardcoreBit.PushesUniform
        (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
          ((yaoSeed Y n (List.ofFn r)).1, (yaoSeed Y n (List.ofFn r)).2.1)) := by
      simp only [yaoCoins_eval]
      convert GarblingProbability.pushesUniform_key_row_blocks (n := n)
        (A := fun i : Fin (Y.circ n).gates.length => Fin ((Y.circ n).gates[i]).args.length → Bool)
        (Y.size_le n) hg
        (fun i a => assignIdx a)
        (fun i a => by change assignIdx a < 4; rw [assignIdx_eq]; exact (hsmall i).1 a)
        (fun i => by simpa only [assignIdx_eq] using (hsmall i).2) using 1
    have hb := uprob_not_good_distinct_le_of_uniform_data
      (nestedSpecial E₁ E₂ n) (Y.circ n)
      (nestedSpecial_decCorrect G₁ G₂ E₁ E₂ hGE₁ hGE₂ n) (hbot n) (Y.fanin n)
      (fun r => yaoSeed Y n (List.ofFn r)) hlaw (Y.outs n) (Y.outs_lt n)
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat, one_div, ← inv_pow] at hb
    refine hb.trans (add_le_add_right ?_ _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hg) (by norm_num))
      (wrongKeyBot_nonneg (nestedSpecial E₁ E₂ n) (hbot n))

/-- **Protocol 162.6 in the OT-hybrid model runs in polynomial time** (the efficiency clause of
[PS10, Definition 155.1], `HybridProtocol.PolyTime`, ruling of 2026-11-05) when `E₁` and `E₂`
are polynomial-time.

**Proof sketch.** The generic garbling program computes Alice's message from the uniform
circuit description and the seed's key, nonce and shift readers. The generic evaluator
computes Bob's reply from arbitrary messages and answers. The interactive-layout
constructor handles every history: Alice sends the garbling or echoes the first message,
and Bob evaluates the first message. The two OT input machines read the appropriate
coin blocks and choice bits through the finite-product call index. The truncation bounds
on ciphertexts give a message envelope independent of the supplied answers. -/
theorem yaoHybrid_polyTime (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    (yaoHybrid Y E₁ E₂).PolyTime (yaoFunctionality Y) := by
  -- Step 1: Alice is efficient. The generic garbling program computes her message from the
  -- uniform circuit description and the seed's key, nonce and shift readers.
  open YaoHybridProof in
  have hAlice : (yaoAlice Y E₁ E₂).Efficient := by
    obtain ⟨gen, hgen, hgenEq⟩ := Y.uniform
    have hdesc n : gen (List.replicate n true) = pairEncode (Y.circ n).encode
        (BinArith.encWords (List.ofFn fun j => encodeNat (Y.outs n j))) := by
      simpa only [encodeCircuit_eq, encodeMsgs_eq_encWords] using hgenEq n
    have hfan n (i : Fin (Y.circ n).gates.length) :
        ((Y.circ n).gates[i]).args.length ≤ 2 :=
      ((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _
        (List.getElem_mem i.isLt)
    have hN := EncodingMachines.unaryLength_poly GI.argX_poly
    have hA := (polyTimeComputable_unaryPoly Y.inA).comp' GI.argX_poly
    have hB := (polyTimeComputable_unaryPoly Y.inB).comp' GI.argX_poly
    have hp := AliceProgram.message_poly hE₁ hE₂
      (fun w => (GI.argX w).length) (fun w => Y.sizeBound.eval (GI.argX w).length)
      (fun w => Y.inA.eval (GI.argX w).length + Y.inB.eval (GI.argX w).length)
      (fun w => Y.inA.eval (GI.argX w).length) (fun w => Y.outLen.eval (GI.argX w).length)
      (fun w => gen (List.replicate (GI.argX w).length true))
      (fun w => pairFstD (GI.argZ w)) NUPPT.inCoins
      hN ((polyTimeComputable_unaryPoly Y.sizeBound).comp' GI.argX_poly)
      (EncodingMachines.unaryAdd_poly hA hB) hA
      ((polyTimeComputable_unaryPoly Y.outLen).comp' GI.argX_poly)
      (hgen.comp' hN) (polyTimeComputable_pairFstD.comp' GI.argZ_poly)
      NUPPT.polyTimeComputable_inCoins
      (fun w => Y.circ (GI.argX w).length)
      (fun w => yaoSeed Y (GI.argX w).length (NUPPT.inCoins w))
      (fun w => Y.outs (GI.argX w).length) (fun w => hdesc _)
      (fun _ => Nat.le_add_right _ _) (fun w => Y.outs_lt _) (fun w => hfan _)
      (fun w v hv b => by rw [keyAt_yaoSeed Y _ _ hv]; rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    -- Step 2: the interactive-layout constructor covers every history: Alice sends this
    -- garbling on the empty history and echoes the first received message otherwise.
    apply firstThenEcho_efficient (yaoAlice Y E₁ E₂)
      (fun x z r => yaoMsg Y E₁ E₂ x.length (pairFstD z) r)
      (yaoAlice_next_nil Y E₁ E₂) (yaoAlice_next_cons Y E₁ E₂)
    refine hp.congr fun w => ?_
    simp only [yaoMsg_eq, yaoTables_eq, yaoKeysA_eq, yaoPairs_eq, encodeMsgs_eq_encWords]
  -- Step 3: Bob is efficient. The generic evaluator computes his reply from arbitrary
  -- messages and answers.
  have hBob : (yaoBob Y E₁ E₂).Efficient := by
    obtain ⟨gen, hgen, hgenEq⟩ := Y.uniform
    have hdesc n : gen (List.replicate n true) = pairEncode (Y.circ n).encode
        (BinArith.encWords (List.ofFn fun j => encodeNat (Y.outs n j))) := by
      simpa only [encodeCircuit_eq, encodeMsgs_eq_encWords] using hgenEq n
    let msg := fun w => pairFstD (GI.argM w)
    let ans := fun w => pairSndD (GI.argZ w)
    have hp := BobProgram.output_poly Y.inA Y.inB Y.outLen Y.circ Y.outs Y.outs_lt
      hgen hdesc hE₁ hE₂ GI.argX_poly
      (polyTimeComputable_pairFstD.comp' GI.argM_poly)
      (polyTimeComputable_pairSndD.comp' GI.argZ_poly)
      (fun w => yaoBobInit Y (GI.argX w).length (msg w) (ans w))
      (fun w => yaoBobTables Y (GI.argX w).length (msg w))
      (fun w => decodeMsgs (pairSndD (pairSndD (msg w))))
      (fun w => by
        dsimp only
        rw [BobInit.initWords_layout, yaoBobInit_eq, List.map_ofFn]
        simp only [List.length_replicate]
        apply congrArg BinArith.encWords
        apply congrArg List.ofFn
        funext v
        simp only [Function.comp_apply, Fin.coe_cast]
        split_ifs
        · apply congrArg List.ofFn
          funext t
          simp only [padFin_apply, Fin.coe_cast, msg]
          rfl
        · rfl)
      (fun w => by simp only [yaoBobInit_eq, List.length_ofFn])
      (fun w v => by simp only [yaoBobTables_eq]; rfl) (fun _ => rfl)
    -- Step 4: the interactive-layout constructor covers every history: Bob evaluates its
    -- first message.
    apply reply_efficient (yaoBob Y E₁ E₂)
      (fun x z a => yaoBobOut Y E₁ E₂ x.length a (pairSndD z))
      (yaoBob_next Y E₁ E₂)
    refine hp.congr fun w => ?_
    simp only [yaoBobOut_eq, yaoBobValues_eq, decodeOut_eq, msg, ans]
  -- Step 5: by `HybridProtocol.polyTime_iff`, it remains to give the two OT call-input
  -- machines and the message envelope.
  apply (HybridProtocol.polyTime_iff (yaoHybrid Y E₁ E₂) (yaoFunctionality Y)).mpr
  refine ⟨hAlice, hBob,
    ⟨OTInputs.otInputA Y.inA Y.sizeBound,
      OTInputs.polyTimeComputable_otInputA Y.inA Y.sizeBound, ?_⟩,
    ⟨OTInputs.otInputB, OTInputs.polyTimeComputable_otInputB, ?_⟩, ?_⟩
  -- Step 6: for call `(i, t)`, Alice's OT input machine reads bit `t` of both keys of wire
  -- `inA + i` from the seed's coin blocks, through the finite-product call index.
  · intro n x r j
    have hlen : otFunctionality.inA.eval n = 2 := by
      rw [otFunctionality_inA, PolyExpr.eval_const]
    rw [List.ofFn_congr hlen]
    apply CallEquations.inputA_eq Y.inA Y.sizeBound n (Y.inB.eval n) x r
    intro i t c
    rw [yaoHybrid_callA, yaoCall_finProdFinEquiv]
    rw [keyAt_yaoSeed Y n r (by
      rw [DAGCircuit.size_eq]
      have := i.isLt
      omega), readBits_apply]
    simp only [Nat.add_assoc]
  -- Step 7: for call `(i, t)`, Bob's OT input machine reads his choice bit `y_i`, through the
  -- finite-product call index.
  · intro n x r j
    have hlen : otFunctionality.inB.eval n = 1 := by
      rw [otFunctionality_inB, PolyExpr.eval_const]
    rw [List.ofFn_congr hlen]
    apply CallEquations.inputB_eq n (Y.inB.eval n) x r
    intro i t c
    rw [yaoHybrid_callB, yaoCall_finProdFinEquiv]
  -- Step 8: the truncation bounds on ciphertexts bound Alice's message, Bob's reply has
  -- `outLen` bits, and the two-move bound gives an envelope independent of the answers.
  · have hfan n (i : Fin (Y.circ n).gates.length) :
        ((Y.circ n).gates[i]).args.length ≤ 2 :=
      ((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _
        (List.getElem_mem i.isLt)
    have hLA (w z r : List Bool) :
        (yaoMsg Y E₁ E₂ w.length (pairFstD z) r).length ≤
          (aliceMessageBound Y.sizeBound Y.inA Y.outLen).eval w.length := by
      rw [yaoMsg_eq, aliceMessageBound_eq]
      apply length_message_of_parts_le
      · rw [yaoTables_eq]
        have ht := length_encoded_garbledTables_le E₁ E₂ w.length
          (Y.circ w.length) (yaoSeed Y w.length r) (hfan w.length)
        have hs := Y.size_le w.length
        rw [DAGCircuit.size_eq] at hs
        exact ht.trans (Nat.mul_le_mul_right _ (by omega))
      · rw [yaoKeysA_eq]
        exact length_encoded_keys_le _
      · rw [yaoPairs_eq]
        exact length_encoded_pairs_le _
    have hLB (w z r a : List Bool) :
        (yaoBobOut Y E₁ E₂ w.length a (pairSndD z)).length ≤ Y.outLen.eval w.length := by
      rw [yaoBobOut_eq, List.length_ofFn]
    refine ⟨.add (aliceMessageBound Y.sizeBound Y.inA Y.outLen) Y.outLen, ?_⟩
    intro n x y aA aB r msg hm
    have h := twoMove_message_length_le (yaoMain Y E₁ E₂)
      (fun w z r => yaoMsg Y E₁ E₂ w.length (pairFstD z) r)
      (fun w z _ a => yaoBobOut Y E₁ E₂ w.length a (pairSndD z))
      (yaoMain_rounds Y E₁ E₂) (yaoMain_verifierFirst Y E₁ E₂)
      (fun _ _ _ => yaoAlice_next_nil Y E₁ E₂ _ _ _)
      (fun _ _ _ _ => yaoBob_next Y E₁ E₂ _ _ _ _)
      (aliceMessageBound Y.sizeBound Y.inA Y.outLen) Y.outLen hLA hLB
      (List.replicate n true) (pairEncode (List.ofFn x) (List.ofFn aA))
      (pairEncode (List.ofFn y) (List.ofFn aB)) r msg hm
    simpa only [List.length_replicate] using h

include hGE₁ hGE₂ in
/-- **The simulators of Theorem 163.7, in the OT-hybrid model** [PS10, Theorem 163.7]: with
nested special encryption from two PRFs `G₁`, `G₂` with polynomial-time evaluators `E₁`, `E₂`,
which are also jointly pseudorandom under one key, there are non-uniform PPT simulators `S_A`,
`S_B` such that for every non-uniform PPT distinguisher there is a negligible `ε` bounding, for
all `n`, `x`, `y`, its advantage between the hybrid real and ideal samplers on both sides.

**Deviation: the joint PRF hypothesis `hG₁₂`** (the pair `k ↦ (G₁(k, ·), G₂(k, ·))` is one PRF;
it implies `hG₁` and `hG₂`). [PS10] doubly encrypts with one scheme. Here the two layers use two
PRFs (`nestedSpecial`), and a wire's key keys `G₂` where the wire is a first argument and `G₁`
where it is a second or only one. The hybrid of step 3 then needs encryptions of both schemes
under one unknown key. A reduction to the security of `G₁` alone cannot produce the `G₂`-pads
under that key, nor conversely; the two separate PRF assumptions do not give their security
under a shared key in general.

**Proof sketch.** Fix the uniform copying simulator for Alice and fake garbler for Bob.
The frozen good-seed statement supplies one negligible bad-event bound before any inputs.
Outside that event, correctness gives both prescribed functionality outputs.
The copying-view coupling simulates Alice; the same event permits Bob's output switch.
The actual two-message view and ideal OT answers identify Bob's selected-key real view.
An exact permutation of the full coin tape identifies this view with stage zero.
The gate hybrid has two substeps per gate, replacing rows under an inactive argument key.
Each neighbor reduces to the frozen joint multi-message encryption statement.
Coordinate swapping preserves the seed law, and reconstruction gives the exact challenge.
Finite worst-input and stage advice yields a negligible bound uniform over both inputs.
The last-stage payload is the fixed Bob simulator's canonical prescribed-output view.
Exact endpoint transport and the statistical bound give their negligible sum for both sides. -/
theorem yaoHybrid_simulators (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))) :
    ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
        (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool),
        distAdv ((yaoHybrid Y E₁ E₂).realA (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv ((yaoHybrid Y E₁ E₂).realB (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
  open YaoHybridProof in
  classical
  have hFan n (i : Fin (Y.circ n).gates.length) :=
    ((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _ (List.getElem_mem i.isLt)
  have hSeedK := yaoSeed_fst Y
  have hSeedR₀ := fun n q i a => congrArg Prod.fst (yaoSeed_snd_fst Y n q i a)
  have hSeedR₁ := fun n q i a => congrArg Prod.snd (yaoSeed_snd_fst Y n q i a)
  obtain ⟨gen, hgen, hgenEq⟩ := Y.uniform
  obtain ⟨SB, hSBuniform, hSBcoins, _, hIdeal⟩ := FakeSimulatorFactory.exists_simulator
    (E₁ := E₁) (E₂ := E₂) (E₁_poly := hE₁) (E₂_poly := hE₂)
    (bound := Y.sizeBound) (inputs := .add Y.inA Y.inB) (inA := Y.inA) (inB := Y.inB)
    (outLen := Y.outLen) (gen := gen) (gen_poly := hgen) (circuit := Y.circ)
    (output := Y.outs) (output_lt := Y.outs_lt) (seed := yaoSeed Y) (fanin := hFan)
    (shape := fun n => by
      simpa only [encodeCircuit_eq, encodeMsgs_eq_encWords] using hgenEq n)
    (input_range := fun n => Nat.le_refl (Y.inA.eval n + Y.inB.eval n))
    (key := by intro n q w hw b; funext t; rw [keyAt_eq, dif_pos hw, hSeedK, readBits_apply])
    (nonce₀ := by intro n q i a t; simp only [hSeedR₀, readBits_apply, assignIdx_eq])
    (nonce₁ := by intro n q i a t; simp only [hSeedR₁, readBits_apply, assignIdx_eq])
    (permutation := by
      intro n q i a t; simp only [yaoSeed_snd_snd, xorShift_apply, readBits_apply])
    (coins := yaoCoins Y)
  obtain ⟨δ, hδ, hWHP⟩ := yaoSeed_good_whp Y E₁ E₂ G₁ G₂ hGE₁ hGE₂ hG₁ hG₂
  let BadWord n q := ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n q) ∧
    ∀ j, keyAt (Y.circ n) (yaoSeed Y n q) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n q) (Y.outs n j) true)
  let switched n x y := fun r : (yaoHybrid Y E₁ E₂).Coins n => pairEncode
    ((yaoHybrid Y E₁ E₂).main.viewV (List.replicate n true)
      ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y)
        (List.ofFn r.1) (List.ofFn r.2))
      ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y)
        (List.ofFn r.1) (List.ofFn r.2)) r).encode
    (List.ofFn ((yaoFunctionality Y).f n x y).1)
  let v n (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) w :=
    ((Y.circ n).values (Fin.append x y)).getD w false
  let game n x y stage := fun r :
      Fin (10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n) → Bool =>
    GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r))
      (Y.inA.eval n) (Y.inB.eval n) (Y.outLen.eval n) (Y.outs n) (v n x y)
      (List.replicate n true) (List.ofFn y) [] (List.ofFn (Y.output n x y)) stage
  have hAlice := AliceStatistical.distAdv_real_ideal_le (yaoHybrid Y E₁ E₂)
    (yaoFunctionality Y) (yaoCoins Y) rfl (yaoMain_rounds Y E₁ E₂)
    (yaoMain_verifierFirst Y E₁ E₂) BadWord δ hWHP (fun _ _ _ => rfl)
    (fun n x y r hr => (yaoHybrid_correct Y E₁ E₂ n x y r
      (not_not.mp hr).1 (not_not.mp hr).2).1)
  have hSwitch := BobStatistical.statClose_real_output_switch
    (yaoHybrid Y E₁ E₂) (yaoFunctionality Y) (yaoCoins Y) rfl BadWord δ hWHP
    (fun n x y r hr => (yaoHybrid_correct Y E₁ E₂ n x y r
      (not_not.mp hr).1 (not_not.mp hr).2).2)
  -- The joint slice-security consumer supplies the complete computational hybrid.
  have hBob : ∀ D : NUPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n x y,
      distAdv (game n x y 0) (game n x y (2 * (Y.circ n).gates.length))
        (D.distinguisherL n) ≤ μ n := by
    intro D
    obtain ⟨μ, hμ, hBound⟩ := GateHybridSecurity.endpoint_negligible
      (L := .add (.add .var .var) (.add .var innerLen))
      (I := fun n => (Fin (Y.inA.eval n) → Bool) × (Fin (Y.inB.eval n) → Bool))
      Y.circ Y.sizeBound Y.inA Y.inB Y.outLen Y.outLen (yaoSeed Y)
      (fun n z => v n z.1 z.2) Y.outs (fun _ z => List.ofFn z.2)
      (fun n z => List.ofFn (Y.output n z.1 z.2)) Y.size_le Y.fanin
      (fun n z => GateHybrids.values_consistent (Y.circ n) (Fin.append z.1 z.2)) Y.outs_sink
      (fun n z => by simp only [List.length_ofFn, le_refl])
      (fun n z => by simp only [List.length_ofFn, le_refl])
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x)) G₁ G₂ E₁ E₂ hE₂
      (fun n s x => List.ofFn_fin_append (G₁ n s x) (G₂ n s x)) hGE₁ hGE₂
      (fun n => by
        simp only [PolyExpr.eval_add, innerLen_eq, PolyExpr.eval_mul,
          PolyExpr.eval_const, PolyExpr.eval_var]
        omega)
      (sliceMultiMessageSecure_of_prfOut hG₁₂)
      (fun n q w b t => by rw [hSeedK, readBits_apply])
      (fun n q i a t => by simp only [hSeedR₀, readBits_apply, assignIdx_eq])
      (fun n q i a t => by simp only [hSeedR₁, readBits_apply, assignIdx_eq])
      (fun n q i a t => by simp only [yaoSeed_snd_snd, xorShift_apply, readBits_apply]) D
    exact ⟨μ, hμ, fun n x y => hBound n (x, y)⟩
  refine ⟨AliceSimulator.simulator (yaoCoins Y), SB, simulators_of_output_switch
    (yaoHybrid Y E₁ E₂) (yaoFunctionality Y) _ SB switched δ hδ hAlice hSwitch ?_⟩
  intro D; obtain ⟨μ, hμ, hBound⟩ := hBob D
  refine ⟨μ, hμ, ?_⟩; intro n x y
  have hvA (i : Fin (Y.inA.eval n)) : v n x y i = (List.ofFn x).getD i false := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn]
    simpa only [Fin.coe_castAdd, Fin.append_left] using
      (Y.circ n).values_getD_input (Fin.append x y) (Fin.castAdd (Y.inB.eval n) i)
  have hvB (i : Fin (Y.inB.eval n)) : v n x y (Y.inA.eval n + i) =
      (List.ofFn y).getD i false := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn]
    simpa only [Fin.coe_natAdd, Fin.append_right] using
      (Y.circ n).values_getD_input (Fin.append x y) (Fin.natAdd (Y.inA.eval n) i)
  have hStart := BobStageZero.acceptProb_eq_stage0 (Y.circ n) (Y.sizeBound.eval n) n
    (hFan n) (v n x y) (Y.size_le n) (yaoSeed Y n)
    (fun q w b t => by rw [hSeedK, readBits_apply])
    (fun q i a t => by simp only [hSeedR₀, readBits_apply, assignIdx_eq])
    (fun q i a t => by simp only [hSeedR₁, readBits_apply, assignIdx_eq])
    (fun q i a t => by simp only [yaoSeed_snd_snd, xorShift_apply, readBits_apply])
    (nestedSpecial E₁ E₂ n) (Y.inA.eval n) (Y.inB.eval n) (Y.outLen.eval n) (Y.outs n)
    (yaoHybrid Y E₁ E₂) (yaoMsg Y E₁ E₂) rfl rfl rfl (yaoAlice_next_nil Y E₁ E₂)
    (List.ofFn x) (List.ofFn y) (List.ofFn ((yaoFunctionality Y).f n x y).1)
    (by rw [Strategy.coinLen_eq, List.length_replicate, yaoHybrid_main, yaoMain_P,
      yaoAlice_coins, yaoCoins_eval])
    (by rw [yaoHybrid_calls, PolyExpr.eval_mul, PolyExpr.eval_var]) hvB
    (fun q r => yaoHybrid_answersB_getD Y E₁ E₂ n _ _ q r)
    (fun r => by simp only [yaoMsg_eq, yaoTables_eq, yaoKeysA_eq, yaoPairs_eq,
      encodeMsgs_eq_encWords, ← hvA]) (D.distinguisherL n)
  let e := (Equiv.arrowCongr (finCongr (yaoCoins_eval Y n).symm) (Equiv.refl Bool)).trans
    (NUPPT.coinsEquivPoly hSBcoins n).symm
  have hEnd := SamplerEndpoints.acceptProb_end_eq_ideal (nestedSpecial E₁ E₂ n) (Y.circ n)
    (fun r => yaoSeed Y n (List.ofFn r)) (Y.inA.eval n) (Y.inB.eval n) (Y.outLen.eval n)
    (Y.outs n) (v n x y) (fun j => (List.ofFn ((yaoFunctionality Y).f n x y).2).getD j false)
    (fun j => by
      change v n x y (Y.outs n j) =
        (List.ofFn ((yaoFunctionality Y).f n x y).2).getD j false
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),
        List.getElem_ofFn]; rfl) (List.replicate n true) (List.ofFn y) []
    (List.ofFn ((yaoFunctionality Y).f n x y).1) e ((yaoFunctionality Y).idealB SB n x y)
    (fun r => by
      simpa only [e, Equiv.trans_apply, NUPPT.coinsEquivPoly_symm_ofFn,
        ofFn_arrowCongr_finCongr] using
        (hIdeal (yaoFunctionality Y) n x y (e r))) (D.distinguisherL n)
  rw [distAdv_def, hStart, ← hEnd]
  have hb := hBound n x y
  rw [distAdv_def] at hb
  exact hb

include hGE₁ hGE₂ in
/-- **Theorem 163.7 in the OT-hybrid model** [PS10, Theorem 163.7; Gol04, §7.3]: for a uniform
fan-in-two circuit family whose output vertices are sinks, and nested special encryption from two
pseudorandom function families `G₁`, `G₂` with polynomial-time evaluators `E₁`, `E₂`, jointly
pseudorandom under one key, Protocol 162.6 in the OT-hybrid model is an honest-but-curious secure
protocol for the family's functionality. The real protocol (composition with Protocol 160.4) is
not in this file.

**Deviation.** The joint PRF hypothesis `hG₁₂` (see `yaoHybrid_simulators`).

Proved from `yaoHybrid_polyTime` and `yaoHybrid_simulators`. -/
theorem yaoHybrid_hbcSecure (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))) :
    (yaoHybrid Y E₁ E₂).HBCSecure (yaoFunctionality Y) :=
  (HybridProtocol.hbcSecure_iff (yaoHybrid Y E₁ E₂) (yaoFunctionality Y)).mpr
    ⟨yaoHybrid_polyTime Y E₁ E₂ hE₁ hE₂,
      yaoHybrid_simulators Y E₁ E₂ G₁ G₂ hGE₁ hGE₂ hE₁ hE₂ hG₁ hG₂ hG₁₂⟩

end Security

end TCSlib.Cryptography.SecureComputation
```

## ===== TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobIO.lean (Lean, at 355a0288d56290e8c984228cbc1824187029e456) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reading the output of an encoded garbled evaluation

The output reader takes a context `⟨1^n, ⟨values, ⟨pairs, outputs⟩⟩⟩`. The value list and
pair list use `BinArith.encWords`; the output-vertex list uses that encoding on unary numbers
with their terminating `false` bit. Every raw input has a total interpretation. A missing key
is padded to `n` bits before it is compared with the decoding pair.

## Main definitions

* `outputBit`: decode one output vertex, given its unary position in the output list.
* `outputWord`: decode a polynomial number of output positions.

## Main results

* `outputBit_poly`: the one-bit output reader is polynomial-time on every word.
* `outputWord_poly`: a polynomial number of decoded output bits is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (reading the output of the garbled circuit).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO

open Complexity Turing

/-- On `⟨⟨u, ⟨values, ⟨pairs, outputs⟩⟩⟩, 1^j⟩`, read output vertex `outputs[j]`, pad its
key from `values` to `|u|` bits, and decode it against `pairs[j]`: first key gives `false`,
otherwise equality to the second key gives `true`. All projections and lookups are total.
`outputBit z = let ctx := pairFstD z; let j := pairSndD z; let vals := pairFstD (pairSndD ctx); let
pairs := pairFstD (pairSndD (pairSndD ctx)); let outs := pairSndD (pairSndD (pairSndD ctx)); let v
:= BinArith.uHead (BinArith.getW (pairEncode j outs)); let k := EnsembleLemmas.padL (pairFstD
ctx).length (BinArith.getW (pairEncode v vals)); let p := BinArith.getW (pairEncode j pairs); if k =
pairFstD p then false else decide (k = pairSndD p)`. -/
def outputBit (z : List Bool) : Bool :=
  let ctx := pairFstD z
  let j := pairSndD z
  let vals := pairFstD (pairSndD ctx)
  let pairs := pairFstD (pairSndD (pairSndD ctx))
  let outs := pairSndD (pairSndD (pairSndD ctx))
  let v := BinArith.uHead (BinArith.getW (pairEncode j outs))
  let k := EnsembleLemmas.padL (pairFstD ctx).length (BinArith.getW (pairEncode v vals))
  let p := BinArith.getW (pairEncode j pairs)
  if k = pairFstD p then false else decide (k = pairSndD p)

/-- The bit reader is the comparison of the padded value at the selected output vertex
with the two components of the selected decoding pair.
`outputBit z = let ctx := pairFstD z; let j := pairSndD z; let vals := pairFstD (pairSndD ctx); let
pairs := pairFstD (pairSndD (pairSndD ctx)); let outs := pairSndD (pairSndD (pairSndD ctx)); let v
:= BinArith.uHead (BinArith.getW (pairEncode j outs)); let k := EnsembleLemmas.padL (pairFstD
ctx).length (BinArith.getW (pairEncode v vals)); let p := BinArith.getW (pairEncode j pairs); if k =
pairFstD p then false else decide (k = pairSndD p)`. -/
theorem outputBit_eq (z : List Bool) :
    outputBit z =
      let ctx := pairFstD z
      let j := pairSndD z
      let vals := pairFstD (pairSndD ctx)
      let pairs := pairFstD (pairSndD (pairSndD ctx))
      let outs := pairSndD (pairSndD (pairSndD ctx))
      let v := BinArith.uHead (BinArith.getW (pairEncode j outs))
      let k := EnsembleLemmas.padL (pairFstD ctx).length (BinArith.getW (pairEncode v vals))
      let p := BinArith.getW (pairEncode j pairs)
      if k = pairFstD p then false else decide (k = pairSndD p) := rfl

/-- The output word at context `z` has `p(|fst z|)` bits; bit `j` is
`outputBit ⟨z, 1^j⟩`. [PS10, Protocol 162.6]
`outputWord p z = List.ofFn fun j : Fin (p.eval (pairFstD z).length) => outputBit (pairEncode z
(List.replicate j true))`. -/
def outputWord (p : PolyExpr) (z : List Bool) : List Bool :=
  List.ofFn fun j : Fin (p.eval (pairFstD z).length) =>
    outputBit (pairEncode z (List.replicate j true))

/-- The output reader's word is the list of `outputBit ⟨z, 1^j⟩` for
`j < p(|fst z|)`. -/
theorem outputWord_eq (p : PolyExpr) (z : List Bool) :
    outputWord p z = List.ofFn fun j : Fin (p.eval (pairFstD z).length) =>
      outputBit (pairEncode z (List.replicate j true)) := rfl

/-- The one-bit output reader is polynomial-time on every raw word:
`PolyTimeComputable (fun z => [outputBit z])`.

**Proof sketch.** Use unary word-list lookup for the output vertex and the decoding pair.
The vertex's key is another word-list lookup, padded to the parameter length. Two word
comparisons implement the decoding rule. Each lookup and padding operation is total, so
malformed words require no separate machine. -/
theorem outputBit_poly : PolyTimeComputable fun z => [outputBit z] := by
  -- Step 1: the value list, decoding pairs and output vertices are projections of the context.
  let ctx := pairFstD
  let vals := fun z => pairFstD (pairSndD (ctx z))
  let pairs := fun z => pairFstD (pairSndD (pairSndD (ctx z)))
  let outs := fun z => pairSndD (pairSndD (pairSndD (ctx z)))
  have hc : PolyTimeComputable ctx := polyTimeComputable_pairFstD
  have hv : PolyTimeComputable vals :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hc)
  have hp : PolyTimeComputable pairs :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hc))
  have ho : PolyTimeComputable outs :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hc))
  -- Step 2: unary word-list lookup gives the output vertex.
  let vertex := fun z => BinArith.uHead (BinArith.getW (pairEncode (pairSndD z) (outs z)))
  have hvertex : PolyTimeComputable vertex := BinArith.polyTimeComputable_uHead.comp
    (BinArith.polyTimeComputable_getW.comp (polyTimeComputable_pairSndD.pairEncode ho))
  -- Step 3: the vertex's key is another word-list lookup, padded to the parameter length.
  let key := fun z => EnsembleLemmas.padL (pairFstD (ctx z)).length
    (BinArith.getW (pairEncode (vertex z) (vals z)))
  have hk0 := EnsembleLemmas.polyTimeComputable_padL .var
    (u := fun z => pairFstD (ctx z))
    (a := fun z => BinArith.getW (pairEncode (vertex z) (vals z)))
    (polyTimeComputable_pairFstD.comp' hc)
    (BinArith.polyTimeComputable_getW.comp' (hvertex.pairEncode hv))
  have hk : PolyTimeComputable key := hk0.congr (g := key) fun z => by
    simp only [key, PolyExpr.eval_var]
  -- Step 4: unary word-list lookup gives the decoding pair.
  let pair := fun z => BinArith.getW (pairEncode (pairSndD z) (pairs z))
  have hpair : PolyTimeComputable pair :=
    BinArith.polyTimeComputable_getW.comp (polyTimeComputable_pairSndD.pairEncode hp)
  -- Step 5: two word comparisons and a branch implement the decoding rule.
  have heq0 : PolyTimeComputable fun z => [decide (key z = pairFstD (pair z))] :=
    (polyTimeComputable_pairEq.comp
      (hk.pairEncode (polyTimeComputable_pairFstD.comp hpair))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have heq1 : PolyTimeComputable fun z => [decide (key z = pairSndD (pair z))] :=
    (polyTimeComputable_pairEq.comp
      (hk.pairEncode (polyTimeComputable_pairSndD.comp hpair))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  refine (polyTimeComputable_ite heq0 (polyTimeComputable_const [false]) heq1).congr
    (g := fun z => [outputBit z]) ?_
  -- Step 6: on every raw word the branch is `[outputBit z]`, by the reader `outputBit_eq`;
  -- every lookup and padding operation is total, so malformed words need no separate case.
  intro z
  by_cases h : key z = pairFstD (pair z) <;>
    simp only [outputBit_eq, ctx, vals, pairs, outs, vertex, key, pair] at h ⊢ <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true,
      if_true, if_false]

/-- The decoded output word has exactly `p(|fst z|)` bits.
`(outputWord p z).length = p.eval (pairFstD z).length`. -/
theorem length_outputWord (p : PolyExpr) (z : List Bool) :
    (outputWord p z).length = p.eval (pairFstD z).length := List.length_ofFn

/-- Reading position `j` of the output word gives `outputBit ⟨z, 1^j⟩` in range and
`false` otherwise.
`(outputWord p z).getD j false = if j < p.eval (pairFstD z).length then outputBit (pairEncode z
(List.replicate j true)) else false`. -/
theorem outputWord_getD (p : PolyExpr) (z : List Bool) (j : ℕ) :
    (outputWord p z).getD j false =
      if j < p.eval (pairFstD z).length then
        outputBit (pairEncode z (List.replicate j true)) else false := by
  rw [outputWord_eq, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

/-- Decoding `p(|fst z|)` output bits is polynomial-time on every context word:
`PolyTimeComputable (outputWord p)`.

**Proof sketch.** The length of the output is the unary polynomial evaluator at the
parameter word. The output bit at a unary index is the polynomial-time bit reader, guarded
by the test that the index is below this length. Apply the published construction of a word
from its polynomial-time length and indexed-bit function. -/
theorem outputWord_poly (p : PolyExpr) : PolyTimeComputable (outputWord p) := by
  have hn : PolyTimeComputable fun w =>
      List.replicate (p.eval (pairFstD (pairSndD w)).length) true :=
    (polyTimeComputable_unaryPoly p).comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have ht := EncodingMachines.ltTest_poly
    (EncodingMachines.unaryLength_poly polyTimeComputable_pairFstD) hn
  have hb : PolyTimeComputable fun w =>
      [outputBit (pairEncode (pairSndD w)
        (List.replicate (pairFstD w).length true))] :=
    outputBit_poly.comp (polyTimeComputable_pairSndD.pairEncode
      (polyTimeComputable_unary.comp polyTimeComputable_pairFstD))
  refine EncodingMachines.polyTimeComputable_of_getD (F := outputWord p) ?_ ?_
  · refine (polyTimeComputable_ite ht hb (polyTimeComputable_const [false])).congr ?_
    intro w
    by_cases h : (pairFstD w).length < p.eval (pairFstD (pairSndD w)).length <;>
      simp only [outputWord_getD, h, decide_true, decide_false,
        Bool.false_eq_true, if_true, if_false]
  · exact ((polyTimeComputable_unaryPoly p).comp polyTimeComputable_pairFstD).congr
      fun z => by simp only [Function.comp_apply, length_outputWord]

/-- On encoded `n`-bit values, decoding pairs and unary output vertices, the bit reader
compares the value at `outs j` with the `j`-th pair. The vertex must be in the value list.
`outputBit (pairEncode (pairEncode (List.replicate n true) (pairEncode (BinArith.encWords (vs.map
List.ofFn)) (pairEncode (BinArith.encWords ps) (BinArith.encWords (List.ofFn fun i =>
BoolCircuit.encodeNat (outs i)))))) (List.replicate j true)) = if List.ofFn (vs.getD (outs j)
default) = pairFstD (ps.getD j []) then false else decide (List.ofFn (vs.getD (outs j) default) =
pairSndD (ps.getD j []))`.

**Proof sketch.** The public word-list lookup equations read the output vertex and the
pair. The vertex is encoded in unary, so its leading ones give its value. In-range lookup
in the encoded value list returns the list of the selected bit vector, and padding this
list leaves it unchanged. -/
theorem outputBit_layout {n k : ℕ} (vs : List (Fin n → Bool)) (ps : List (List Bool))
    (outs : Fin k → ℕ) (j : Fin k) (hv : outs j < vs.length) :
    outputBit (pairEncode
        (pairEncode (List.replicate n true) (pairEncode (BinArith.encWords (vs.map List.ofFn))
          (pairEncode (BinArith.encWords ps)
            (BinArith.encWords (List.ofFn fun i => BoolCircuit.encodeNat (outs i))))))
        (List.replicate j true)) =
      if List.ofFn (vs.getD (outs j) default) = pairFstD (ps.getD j []) then false
      else decide (List.ofFn (vs.getD (outs j) default) = pairSndD (ps.getD j [])) := by
  have ho : (List.ofFn fun i => BoolCircuit.encodeNat (outs i)).getD j [] =
      BoolCircuit.encodeNat (outs j) := by
    rw [List.getD_eq_getElem _ _ (by simpa using j.isLt), List.getElem_ofFn]
  have hk : (vs.map List.ofFn).getD (outs j) [] = List.ofFn (vs.getD (outs j) default) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map,
      List.getD_eq_getElem _ _ hv]
  have hu := BinArith.uHead_encodeNat (outs j) []
  rw [List.append_nil] at hu
  simp only [outputBit_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.getW_pairEncode, List.length_replicate, ho, hu]
  rw [hk, ← EnsembleLemmas.ofFn_padFin_eq_padL, padFin_ofFn]

/-- On encoded `n`-bit values, decoding pairs and `p(n)` unary output vertices,
`outputWord p` is the vector of comparisons with the selected decoding pairs. Every
output vertex must be present in the value list. [PS10, Protocol 162.6]
`outputWord p (pairEncode (List.replicate n true) (pairEncode (BinArith.encWords (vs.map List.ofFn))
(pairEncode (BinArith.encWords ps) (BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat
(outs j)))))) = List.ofFn fun j => if List.ofFn (vs.getD (outs j) default) = pairFstD (ps.getD j [])
then false else decide (List.ofFn (vs.getD (outs j) default) = pairSndD (ps.getD j []))`. -/
theorem outputWord_layout (p : PolyExpr) {n : ℕ} (vs : List (Fin n → Bool))
    (ps : List (List Bool)) (outs : Fin (p.eval n) → ℕ)
    (hv : ∀ j, outs j < vs.length) :
    outputWord p
        (pairEncode (List.replicate n true) (pairEncode (BinArith.encWords (vs.map List.ofFn))
          (pairEncode (BinArith.encWords ps)
            (BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (outs j)))))) =
      List.ofFn fun j =>
        if List.ofFn (vs.getD (outs j) default) = pairFstD (ps.getD j []) then false
        else decide (List.ofFn (vs.getD (outs j) default) = pairSndD (ps.getD j [])) := by
  simp only [outputWord_eq, pairFstD_pairEncode, List.length_replicate, Fin.coe_cast]
  apply congrArg List.ofFn
  funext j
  exact outputBit_layout vs ps outs j (hv j)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO
```

## ===== TCSlib/Cryptography/SecureComputation/Yao/HybridProof/ChunkScanner.lean (Lean, at 355a0288d56290e8c984228cbc1824187029e456) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.TuringMachine.Build.ModuleHost

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite scanners with word-valued emissions

This construction extends the existing one-bit transducer to a bounded word per input bit.
It uses the verified emitting loop, with a three-bit control and a shrinking input suffix.
The circuit-description decoder uses its seven control phases.

## Main definitions

* `ChunkScanner.Phase`: three bits of finite control.
* `ChunkScanner.scan`: concatenate the emitted words while advancing the control.

## Main results

* `ChunkScanner.scan_poly`: every such scanner is polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, §6.2 (descriptions of uniform circuit families).

Generic parsing infrastructure for [AB09, §6.2], circuit descriptions. The machine assembly
uses the emitting-loop host of `Complexity.polyTimeComputable_emitIter`.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner

open Complexity Turing

/-- The scanner has three bits of finite control: `Phase = Bool × Bool × Bool`. -/
abbrev Phase := Bool × Bool × Bool

/-- The phase code is the three-bit word `[q.1, q.2.1, q.2.2]`.
`phaseCode q = [q.1, q.2.1, q.2.2]`. -/
def phaseCode (q : Phase) : List Bool := [q.1, q.2.1, q.2.2]

/-- `phaseCode q = [q.1, q.2.1, q.2.2]`. -/
theorem phaseCode_eq (q : Phase) : phaseCode q = [q.1, q.2.1, q.2.2] := rfl

/-- Every phase code has length three: `|phaseCode q| = 3`. -/
theorem length_phaseCode (q : Phase) : (phaseCode q).length = 3 := rfl

/-- Read the first three bits, defaulting each missing bit to false.
`readPhase w = (w.headD false, (w.drop 1).headD false, (w.drop 2).headD false)`. -/
def readPhase (w : List Bool) : Phase :=
  (w.headD false, (w.drop 1).headD false, (w.drop 2).headD false)

/-- `readPhase w = (head w, head (drop 1 w), head (drop 2 w))`, with false defaults. -/
theorem readPhase_eq (w : List Bool) :
    readPhase w = (w.headD false, (w.drop 1).headD false, (w.drop 2).headD false) := rfl

/-- Reading the phase code recovers the phase: `readPhase (phaseCode q) = q`. -/
theorem readPhase_code (q : Phase) : readPhase (phaseCode q) = q := rfl

/-- Concatenate the word `o q b` emitted at each input bit, changing control by `δ q b`.
`scan δ o q [] = []` and `scan δ o q (b :: w) = o q b ++ scan δ o (δ q b) w`. -/
def scan (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) :
    Phase → List Bool → List Bool
  | _, [] => []
  | q, b :: w => o q b ++ scan δ o (δ q b) w

/-- `scan δ o q [] = []`. -/
theorem scan_nil (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase) :
    scan δ o q [] = [] := rfl

/-- `scan δ o q (b :: w) = o q b ++ scan δ o (δ q b) w`. -/
theorem scan_cons (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase)
    (b : Bool) (w : List Bool) :
    scan δ o q (b :: w) = o q b ++ scan δ o (δ q b) w := rfl

/-- A scanner round stores the next three-bit control and removes one input bit.
`step δ w = pairEncode (phaseCode (δ (readPhase (pairFstD w)) ((pairSndD w).headD false)))
((pairSndD w).drop 1)`. -/
def step (δ : Phase → Bool → Phase) (w : List Bool) : List Bool :=
  pairEncode (phaseCode (δ (readPhase (pairFstD w)) ((pairSndD w).headD false)))
    ((pairSndD w).drop 1)

/-- `step δ w` pairs the next phase code with `(pairSndD w).drop 1`.
`step δ w = pairEncode (phaseCode (δ (readPhase (pairFstD w)) ((pairSndD w).headD false)))
((pairSndD w).drop 1)`. -/
theorem step_eq (δ : Phase → Bool → Phase) (w : List Bool) :
    step δ w =
      pairEncode (phaseCode (δ (readPhase (pairFstD w)) ((pairSndD w).headD false)))
        ((pairSndD w).drop 1) := rfl

/-- A scanner emits nothing on an empty suffix, and otherwise emits `o q (head suffix)`.
`emit o w = if pairSndD w = [] then [] else o (readPhase (pairFstD w)) ((pairSndD w).headD
false)`. -/
def emit (o : Phase → Bool → List Bool) (w : List Bool) : List Bool :=
  if pairSndD w = [] then [] else o (readPhase (pairFstD w)) ((pairSndD w).headD false)

/-- `emit o w` is empty on an empty second component and otherwise is the table entry.
`emit o w = if pairSndD w = [] then [] else o (readPhase (pairFstD w)) ((pairSndD w).headD
false)`. -/
theorem emit_eq (o : Phase → Bool → List Bool) (w : List Bool) :
    emit o w =
      if pairSndD w = [] then []
      else o (readPhase (pairFstD w)) ((pairSndD w).headD false) := rfl

/-- A fixed table of four polynomial-time Boolean tests is polynomial-time.

**Proof sketch.** Branch on the four bits in turn using the existing polynomial-time
conditional combinator. Each of the sixteen leaves is the corresponding constant word;
case analysis on the four bits identifies the resulting decision tree with the table. -/
private theorem table4_poly (F : Bool → Bool → Bool → Bool → List Bool)
    {a b c d : List Bool → Bool}
    (ha : PolyTimeComputable fun w => [a w])
    (hb : PolyTimeComputable fun w => [b w])
    (hc : PolyTimeComputable fun w => [c w])
    (hd : PolyTimeComputable fun w => [d w]) :
    PolyTimeComputable fun w => F (a w) (b w) (c w) (d w) := by
  convert (polyTimeComputable_ite ha
    (polyTimeComputable_ite hb
    (polyTimeComputable_ite hc
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F true true true true))
    (polyTimeComputable_const (F true true true false)))
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F true true false true))
    (polyTimeComputable_const (F true true false false))))
    (polyTimeComputable_ite hc
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F true false true true))
    (polyTimeComputable_const (F true false true false)))
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F true false false true))
    (polyTimeComputable_const (F true false false false)))))
    (polyTimeComputable_ite hb
    (polyTimeComputable_ite hc
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F false true true true))
    (polyTimeComputable_const (F false true true false)))
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F false true false true))
    (polyTimeComputable_const (F false true false false))))
    (polyTimeComputable_ite hc
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F false false true true))
    (polyTimeComputable_const (F false false true false)))
    (polyTimeComputable_ite hd
    (polyTimeComputable_const (F false false false true))
    (polyTimeComputable_const (F false false false false)))))) using 1
  funext w
  cases a w <;> cases b w <;> cases c w <;> cases d w <;> rfl

/-- The three-bit phase type is the Boolean triple: `Phase = Bool × Bool × Bool`. -/
theorem phase_eq : Phase = (Bool × Bool × Bool) := rfl

/-- Each scanner round is polynomial-time: `PolyTimeComputable (step δ)`. -/
theorem step_poly (δ : Phase → Bool → Phase) : PolyTimeComputable (step δ) := by
  exact (table4_poly (fun a b c d => phaseCode (δ (a, b, c) d))
    (polyTimeComputable_headD.comp polyTimeComputable_pairFstD)
    (polyTimeComputable_headD.comp
      ((BinArith.polyTimeComputable_drop 1).comp polyTimeComputable_pairFstD))
    (polyTimeComputable_headD.comp
      ((BinArith.polyTimeComputable_drop 2).comp polyTimeComputable_pairFstD))
    (polyTimeComputable_headD.comp polyTimeComputable_pairSndD)).pairEncode
      (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)

/-- Every finite emission table is polynomial-time: `PolyTimeComputable (emit o)`. -/
theorem emit_poly (o : Phase → Bool → List Bool) : PolyTimeComputable (emit o) := by
  convert polyTimeComputable_ite
    (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_const [])
    (table4_poly (fun a b c d => o (a, b, c) d)
      (polyTimeComputable_headD.comp polyTimeComputable_pairFstD)
      (polyTimeComputable_headD.comp
        ((BinArith.polyTimeComputable_drop 1).comp polyTimeComputable_pairFstD))
      (polyTimeComputable_headD.comp
        ((BinArith.polyTimeComputable_drop 2).comp polyTimeComputable_pairFstD))
      (polyTimeComputable_headD.comp polyTimeComputable_pairSndD)) using 1
  funext w
  simp only [emit_eq, readPhase_eq, decide_eq_true_eq, Function.comp_apply]

/-- On a phase/suffix pair the round advances its phase and drops one suffix bit.
`step δ (pairEncode (phaseCode q) w) = pairEncode (phaseCode (δ q (w.headD false))) (w.drop 1)`. -/
theorem step_pair (δ : Phase → Bool → Phase) (q : Phase) (w : List Bool) :
    step δ (pairEncode (phaseCode q) w) =
      pairEncode (phaseCode (δ q (w.headD false))) (w.drop 1) := by
  rw [step_eq, pairFstD_pairEncode, pairSndD_pairEncode, readPhase_code]

/-- On a phase/suffix pair emission is empty exactly for the exhausted suffix.
`emit o (pairEncode (phaseCode q) w) = if w = [] then [] else o q (w.headD false)`. -/
theorem emit_pair (o : Phase → Bool → List Bool) (q : Phase) (w : List Bool) :
    emit o (pairEncode (phaseCode q) w) =
      if w = [] then [] else o q (w.headD false) := by
  rw [emit_eq, pairFstD_pairEncode, pairSndD_pairEncode, readPhase_code]

/-- The input suffix does not grow in one round:
`|pairSndD (step δ w)| ≤ |pairSndD w|`. -/
theorem length_snd_step (δ : Phase → Bool → Phase) (w : List Bool) :
    (pairSndD (step δ w)).length ≤ (pairSndD w).length := by
  rw [step_eq, pairSndD_pairEncode, List.length_drop]
  omega

/-- Every iterated suffix stays within the original word:
`|pairSndD ((step δ)^[i] w)| ≤ |w|`. -/
theorem length_snd_iterate (δ : Phase → Bool → Phase) (w : List Bool) (i : ℕ) :
    (pairSndD ((step δ)^[i] w)).length ≤ w.length := by
  induction i with
  | zero => exact length_pairSndD_le w
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (length_snd_step δ _).trans ih

/-- Every scanner state has a linear envelope:
`|((step δ)^[i]) w| ≤ 9 · (|w| + 1)`. -/
theorem length_iterate (δ : Phase → Bool → Phase) (w : List Bool) (i : ℕ) :
    ((step δ)^[i] w).length ≤ 9 * (w.length + 1) := by
  cases i with
  | zero => simp only [Function.iterate_zero_apply]; omega
  | succ i =>
    rw [Function.iterate_succ_apply', step_eq, length_pairEncode, length_phaseCode,
      List.length_drop]
    have h := length_snd_iterate δ w i
    omega

/-- Emitting along at least `|w|` rounds of the encoded scanner yields `scan δ o q w`.
`(List.range N).flatMap (fun i => emit o ((step δ)^[i] (pairEncode (phaseCode q) w))) = scan δ o q
w`.

**Proof sketch.** Induct on the round budget. The first round emits the head's table entry,
then the next state holds the remaining input. Once the suffix is empty all later emissions
are empty, so any budget at least the input length gives the same result. -/
theorem flatMap_scan (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool)
    (N : ℕ) (q : Phase) (w : List Bool) (hN : w.length ≤ N) :
    (List.range N).flatMap
        (fun i => emit o ((step δ)^[i] (pairEncode (phaseCode q) w))) =
      scan δ o q w := by
  induction N generalizing q w with
  | zero =>
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hw
    rfl
  | succ N ih =>
    -- Peel the first round and run the remaining budget from the next state.
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Function.iterate_zero_apply, Function.iterate_succ_apply]
    rw [emit_pair, step_pair]
    cases w with
    | nil =>
      simp only [List.headD_nil, List.drop_nil, scan_nil]
      exact ih (δ q false) [] (by simp)
    | cons b w =>
      simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero,
        List.cons_ne_nil, if_false, scan_cons]
      rw [ih (δ q b) w (by simpa using hN)]

/-- A finite word-emitting scanner is polynomial-time:
`PolyTimeComputable (scan δ o q)`.

**Proof sketch.** Use the public emitting-loop host on the encoded phase and suffix.
The round and emission tables are polynomial-time finite Boolean tables; every round's
state length is bounded by `9 · (|input| + 1)`. The initial pair supplies more rounds than
there are input bits, and `flatMap_scan` identifies the emitted word exactly. -/
theorem scan_poly (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase) :
    PolyTimeComputable (scan δ o q) := by
  have h := polyTimeComputable_emitIter (step_poly δ) (emit_poly o) 1 1 9 1
    (fun w i => by simpa only [Nat.pow_one] using length_iterate δ w i)
  have hpre : PolyTimeComputable fun w => pairEncode (phaseCode q) w :=
    (polyTimeComputable_const (phaseCode q)).pairEncode polyTimeComputable_id
  convert h.comp hpre using 1
  funext w
  simp only [Function.comp_apply, Nat.one_mul, Nat.pow_one]
  symm
  apply flatMap_scan
  rw [length_pairEncode]
  omega

/-- One clean finite machine installs the scanner's value and emits nothing within
`A · (|arg| + 1)^d` steps. Every work head of that same machine remains within that bound
at every time. The machine is the public H14 clean-install module for `scan δ o q`.
`∃ (M : FinTM Bool) (A d : ℕ), ModuleHost.Clean M (scan δ o q) (fun _ => []) (fun n => A * (n + 1) ^
d) ∧ ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k), |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀
(stateWord M.k arg)) v).workTapePos j| ≤ (A * (arg.length + 1) ^ d : ℕ)`. -/
theorem scan_host (δ : Phase → Bool → Phase) (o : Phase → Bool → List Bool) (q : Phase) :
    ∃ (M : FinTM Bool) (A d : ℕ),
      ModuleHost.Clean M (scan δ o q) (fun _ => []) (fun n => A * (n + 1) ^ d) ∧
      ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
        |(M.tm.runFrom
          (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
            (A * (arg.length + 1) ^ d : ℕ) := by
  obtain ⟨M, A, d, hM⟩ := ModuleHost.clean_install (scan_poly δ o q)
  exact ⟨M, A, d, hM, fun x arg v j => hM.envelope x arg v j⟩

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.ChunkScanner
```

## ===== TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeProgram.lean (Lean, at 355a0288d56290e8c984228cbc1824187029e456) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AliceProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeObjects
import TCSlib.Cryptography.Asymptotic.OneWay

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time simulated garbling programs

The simulated garbler shares the real garbler's addressed key, nonce, row, and bounded table
machines. Its output-key bit is always false; output decoding pairs use the prescribed
result bits. All circuit families and seed equations remain parameters.

## Main definitions

None.

## Main results

* `FakeProgram.activeAnswers_word`, `activeAnswers_poly`: canonical flat active-key answers.
* `FakeProgram.inputKeys_poly`, `outputPairs_poly`: active input keys and swapped output pairs.
* `FakeProgram.tables_poly`, `message_poly`: the complete actual simulated garbling program.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (simulation for Bob).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

/-- The canonical simulated answer is the concatenation of the false-key blocks beginning
at vertex `first`: `ofFn (activeAnswers C s first count) = flatten (ofFn (ofFn ∘ key0))`.
This reuses the published generic tuple-block identity. [PS10, Theorem 163.7] -/
theorem activeAnswers_word {inputs width : ℕ} {ρ : Type} (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ) :
    List.ofFn (FakeObjects.activeAnswers C s first count) =
      (List.ofFn fun i : Fin count => List.ofFn (keyAt C s (first + i) false)).flatten := by
  have heq : FakeObjects.activeAnswers C s first count =
      (FunFamily.blocks count width).symm (fun i => keyAt C s (first + i) false) := by
    funext t
    rw [FakeObjects.activeAnswers_eq, FunFamily.blocks_symm_apply]
  rw [heq, FunFamily.ofFn_blocks_symm]

/-- The canonical flat false-key answer is polynomial-time from unary width, bound,
starting vertex and count maps, a polynomial-time coin word, a valid input range, and the
seed's addressed-key equation. [PS10, Theorem 163.7]
`PolyTimeComputable fun z => List.ofFn (FakeObjects.activeAnswers (C z) (s z) (first z) (count z))`.

**Proof sketch.** On an indexed retained input, add the unary index to the starting vertex
and read its false-key window. The public data-dependent concatenation loop emits one such
block per requested vertex. The generic tuple-block identity identifies this concatenation
with the canonical finite answer; the valid-range bound justifies every seed key reader. -/
theorem activeAnswers_poly (width bound first count inputs : List Bool → ℕ)
    (coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hfirst : PolyTimeComputable fun z => List.replicate (first z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hrange : ∀ z, first z + count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z =>
      List.ofFn (FakeObjects.activeAnswers (C z) (s z) (first z) (count z)) := by
  let entry := fun z i => RowFromCoins.keyWord width bound (fun v => first v + i)
    (fun _ => false) coins z
  have hv := unaryAdd_poly (hfirst.comp polyTimeComputable_pairSndD)
    (unaryLength_poly polyTimeComputable_pairFstD)
  have he : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length := by
    refine (RowFromCoins.keyWord_poly (hcoins.comp polyTimeComputable_pairSndD)
      (hwidth.comp polyTimeComputable_pairSndD) (hbound.comp polyTimeComputable_pairSndD)
      hv (polyTimeComputable_const [false])).congr fun w => ?_
    simp only [entry, RowFromCoins.keyWord_eq, Function.comp_apply]
  refine (ColMachines.polyTimeComputable_flatMap_range he hcount).congr fun z => ?_
  rw [activeAnswers_word, List.flatMap_def]
  apply congrArg List.flatten
  symm
  apply ofFn_eq_map_range
  intro i
  dsimp only [entry]
  rw [RowFromCoins.keyWord_eq]
  apply congrArg List.ofFn
  apply hkey
  rw [DAGCircuit.size_eq]
  have := hrange z
  omega

/-- Swapping each encoded pair according to the corresponding bit of a polynomial-time
result word preserves polynomial time. The pair vector is supplied by a polynomial-time
canonical encoding, and its unary length is polynomial-time. [PS10, Theorem 163.7]
`PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j => if (result z).getD j false then
pairEncode (value z j).2 (value z j).1 else pairEncode (value z j).1 (value z j).2)`.

**Proof sketch.** At a unary index, read the pair from its canonical word vector and read
the corresponding result bit. A conditional either swaps the two public pair projections
or retains the original pair. The existing indexed word-vector assembler encodes all these
entries; canonical list lookup identifies each entry with the requested pair. -/
theorem swapPairs_poly (count : List Bool → ℕ) (pairs result : List Bool → List Bool)
    (value : ∀ z, Fin (count z) → List Bool × List Bool)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hpairs : PolyTimeComputable pairs) (hresult : PolyTimeComputable result)
    (hshape : ∀ z, pairs z = BinArith.encWords (List.ofFn fun j =>
      pairEncode (value z j).1 (value z j).2)) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j =>
      if (result z).getD j false then pairEncode (value z j).2 (value z j).1
      else pairEncode (value z j).1 (value z j).2) := by
  let lookup := fun z i => BinArith.getW (pairEncode (List.replicate i true) (pairs z))
  let entry := fun z i => if (result z).getD i false then
    pairEncode (pairSndD (lookup z i)) (pairFstD (lookup z i)) else lookup z i
  have hl : PolyTimeComputable fun w => lookup (pairSndD w) (pairFstD w).length :=
    BinArith.polyTimeComputable_getW.comp
      ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).pairEncode
        (hpairs.comp polyTimeComputable_pairSndD))
  have hb : PolyTimeComputable fun w =>
      [(result (pairSndD w)).getD (pairFstD w).length false] :=
    getBit_poly (hresult.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)
  have he : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length :=
    polyTimeComputable_ite hb
      ((polyTimeComputable_pairSndD.comp hl).pairEncode
        (polyTimeComputable_pairFstD.comp hl)) hl
  refine WordLists.ofFnTable_poly _ entry hcount he ?_
  intro z j
  have hlookup : lookup z j = pairEncode (value z j).1 (value z j).2 := by
    dsimp only [lookup]
    rw [hshape z, BinArith.getW_pairEncode, List.length_replicate]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]
  dsimp only [entry]
  rw [hlookup, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The encoded simulated decoding-pair vector is polynomial-time from the real output
pair readers and a polynomial-time prescribed result word. Each result bit swaps the
corresponding two keys. [PS10, Theorem 163.7]
`PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j : Fin (count z) => pairEncode
(List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j) ((result z).getD j false)).1) (List.ofFn
(FakeObjects.decodePair (C z) (s z) (output z j) ((result z).getD j false)).2))`.

**Proof sketch.** Compute the real canonical output-pair vector once. Apply the generic
indexed pair-swap contract to that vector and the result word. A Boolean case split on
each prescribed output bit identifies the swapped pair with the simulated pair reader. -/
theorem outputPairs_poly (width bound count inputs : List Bool → ℕ)
    (description coins result : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (hresult : PolyTimeComputable result) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (count z) → ℕ)
    (houtsWord : ∀ z, pairSndD (description z) =
      BinArith.encWords (List.ofFn fun j => encodeNat (output z j)))
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j : Fin (count z) =>
      pairEncode (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
        ((result z).getD j false)).1)
        (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
          ((result z).getD j false)).2)) := by
  let value := fun z (j : Fin (count z)) =>
    (List.ofFn (keyAt (C z) (s z) (output z j) false),
      List.ofFn (keyAt (C z) (s z) (output z j) true))
  let pairs := fun z => BinArith.encWords (List.ofFn fun j =>
    pairEncode (value z j).1 (value z j).2)
  have hp : PolyTimeComputable pairs := AliceProgram.outputPairs_poly
    width bound count inputs description coins hwidth hbound hcount hdescription hcoins
    C s output houtsWord houtput_lt hkey
  refine (swapPairs_poly count pairs result value hcount hp hresult (fun _ => rfl)).congr
    fun z => ?_
  apply congrArg BinArith.encWords
  apply congrArg List.ofFn
  funext j
  cases hb : (result z).getD j false <;>
    simp [value, FakeObjects.decodePair_eq]

/-- The encoded simulated Alice input-key vector contains the false key at every input
vertex and is polynomial-time under the real selected-key reader hypotheses.
[PS10, Theorem 163.7]
`PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun v : Fin (count z) => List.ofFn (keyAt
(C z) (s z) v false))`. -/
theorem inputKeys_poly (width bound count inputs : List Bool → ℕ)
    (coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hcount_le : ∀ z, count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun v : Fin (count z) =>
      List.ofFn (keyAt (C z) (s z) v false)) := by
  simpa only [List.getD_nil] using AliceProgram.selectedKeys_poly width bound count inputs
    (fun _ => []) coins hwidth hbound hcount (polyTimeComputable_const []) hcoins
    C s hcount_le hkey

/-- The actual encoded simulated table vector is polynomial-time from the generic uniform
circuit-description map and the seed's key, nonce, and XOR-permutation readers. Every row
plaintext is its output vertex's false key. [PS10, Theorem 163.7]
`PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun i => BinArith.encWords
(FakeObjects.table (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i))`.

**Proof sketch.** Decode the canonical circuit description to the public gate-record word.
At a unary index, select its argument-word list and invoke the real garbler's generic row
core with the constant false output bit. The existing guarded table adapter enumerates at
most four rows, and the indexed word-vector assembler traverses all gate records. To prove
correctness, transport the retained context through the generic pointwise table contract.
Canonical record lookup fixes the argument list. Its fan-in bound removes the guard and
normalizes the dependent assignment enumeration. The arbitrary-output-bit row theorem then
identifies every enumerated row with the new simulated semantic object. -/
theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs : List Bool → ℕ)
    (description outs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hshape : ∀ z, description z = pairEncode (C z).encode (outs z))
    (hfan : ∀ z (i : Fin (C z).gates.length), ((C z).gates[i]).args.length ≤ 2)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ z (i : Fin (C z).gates.length) a t, (s z).2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun i =>
      BinArith.encWords (FakeObjects.table (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i)) := by
  -- Step 1: the pieces: the decoded gate-record word, the argument-word list at a unary
  -- index, the real garbler's row core with constant false output bit, and the guarded
  -- table adapter.
  let gates := GarblingProgram.gatesWord description
  let record := fun w => BinArith.getW (pairEncode (pairFstD w) (gates (pairSndD w)))
  let args := fun w => pairSndD (record w)
  let row := fun l a => RowFromCoins.rowWordWith E₁ E₂
    (fun w => width (pairSndD w)) (fun w => bound (pairSndD w))
    (fun w => inputs (pairSndD w)) (fun w => (pairFstD w).length)
    args (fun w => coins (pairSndD w)) (fun _ => false) l a
  let entry := TablesFromCoins.tableWordWith args row
  let entryVal := fun z i => entry (pairEncode (List.replicate i true) z)
  -- Step 2: each piece is polynomial-time; `hgs` reads the decoded word as the encoded gate
  -- records.
  have hgates : PolyTimeComputable gates := GarblingProgram.gatesWord_poly hdescription
  have hgs (z : List Bool) :
      gates z = BinArith.encWords ((C z).gates.map DescriptionDecoder.gateRecord) :=
    GarblingProgram.gatesWord_description description z (C z) (outs z) (hshape z)
  have hrecord := BinArith.polyTimeComputable_getW.comp
    (polyTimeComputable_pairFstD.pairEncode (hgates.comp polyTimeComputable_pairSndD))
  have hargs : PolyTimeComputable args := polyTimeComputable_pairSndD.comp hrecord
  have hentry : PolyTimeComputable entry := TablesFromCoins.tableWordWith_poly row hargs
    (fun l _ a => RowFromCoins.rowWordWith_poly hE₁ hE₂
      (hwidth.comp polyTimeComputable_pairSndD) (hbound.comp polyTimeComputable_pairSndD)
      (hinputs.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD) hargs
      (hcoins.comp polyTimeComputable_pairSndD) (polyTimeComputable_const [false]) l a)
  -- Step 3: the indexed word-vector assembler traverses all gate records; it remains to
  -- identify each entry with its simulated table.
  have hcount : PolyTimeComputable fun z => List.replicate (C z).gates.length true := by
    refine (BinArith.polyTimeComputable_countW.comp hgates).congr fun z => ?_
    rw [Function.comp_apply, BinArith.countW_eq, hgs z,
      BinArith.decWords_encWords, List.length_map]
  have he : PolyTimeComputable fun w => entryVal (pairSndD w) (pairFstD w).length :=
    hentry.comp ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD)
  refine WordLists.ofFnTable_poly _ entryVal hcount he ?_
  -- Step 4: correctness. Transport the retained context through the generic pointwise table
  -- contract `tableWordWith_congr_at`.
  intro z i
  symm
  let w := pairEncode (List.replicate i true) z
  let args' := fun v => pairSndD (BinArith.getW
    (pairEncode (List.replicate i true) (gates v)))
  let row' := fun l a => RowFromCoins.rowWordWith E₁ E₂ width bound inputs
    (fun _ => i) args' coins (fun _ => false) l a
  have ha : args w = args' z := by
    simp only [args, args', record, w, pairFstD_pairEncode, pairSndD_pairEncode]
  have hr : ∀ l a, row l a w = row' l a z := by
    intro l a
    dsimp only [row, row']
    conv_lhs => rw [RowFromCoins.rowWordWith_value]
    conv_rhs => rw [RowFromCoins.rowWordWith_value]
    simp only [args, args', record, w, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate]
  change TablesFromCoins.tableWordWith args row w = _
  rw [TablesFromCoins.tableWordWith_congr_at args args' row row' w z ha hr]
  -- Step 5: canonical record lookup fixes the argument list.
  have hrec : BinArith.getW (pairEncode (List.replicate i true) (gates z)) =
      DescriptionDecoder.gateRecord ((C z).gates[i]) := by
    rw [hgs z, BinArith.getW_pairEncode, List.length_replicate]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact i.isLt), List.getElem_map]
    rfl
  have hcanonical : args' z =
      BinArith.encWords (((C z).gates[i]).args.map fun v => List.replicate v true) := by
    dsimp only [args']
    rw [hrec, DescriptionDecoder.gateRecord_eq, pairSndD_pairEncode]
  -- Step 6: the fan-in bound removes the guard and normalizes the assignment enumeration.
  rw [TablesFromCoins.tableWordWith_of_encoded args' row' z _ (hfan z i) hcanonical,
    FakeObjects.table_eq]
  -- Step 7: the arbitrary-output-bit row theorem identifies every enumerated row with the
  -- simulated row.
  apply congrArg BinArith.encWords
  apply List.map_congr_left
  intro a _
  dsimp only [row']
  rw [FakeObjects.row_eq]
  exact RowFromCoins.rowWordWith_enc E₁ E₂ width bound inputs (fun _ => i) args' coins
    (fun _ => false) z (C z) (s z) i a (hfan z i) rfl hcanonical
    (hkey z) (hr₀ z i) (hr₁ z i) (hperm z i)

/-- The complete simulated Alice message is polynomial-time: simulated tables with false
row plaintexts, Alice's false input keys, and output pairs swapped by the prescribed output
word. The assumptions are the generic uniform-description and seed block readers, valid
input/output ranges, and polynomial-time raw selectors. [PS10, Theorem 163.7]
`PolyTimeComputable fun z => pairEncode (BinArith.encWords (List.ofFn fun i => BinArith.encWords
(FakeObjects.table (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i))) (pairEncode (BinArith.encWords
(List.ofFn fun v : Fin (inA z) => List.ofFn (keyAt (C z) (s z) v false))) (BinArith.encWords
(List.ofFn fun j : Fin (outLen z) => pairEncode (List.ofFn (FakeObjects.decodePair (C z) (s z)
(output z j) ((result z).getD j false)).1) (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z
j) ((result z).getD j false)).2))))`.

**Proof sketch.** The generic simulated-table program computes all false-output-key tables.
The real selected-key contract at a constant false input gives Alice's active input keys.
The real output-pair contract followed by the indexed bit-controlled swap gives the simulated
decoding information. Two applications of the public pairing closure assemble the message. -/
theorem message_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs inA outLen : List Bool → ℕ)
    (description result coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hinA : PolyTimeComputable fun z => List.replicate (inA z) true)
    (houtLen : PolyTimeComputable fun z => List.replicate (outLen z) true)
    (hdescription : PolyTimeComputable description) (hresult : PolyTimeComputable result)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (outLen z) → ℕ)
    (hshape : ∀ z, description z = pairEncode (C z).encode
      (BinArith.encWords (List.ofFn fun j => encodeNat (output z j))))
    (hinA_le : ∀ z, inA z ≤ inputs z)
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hfan : ∀ z (i : Fin (C z).gates.length), ((C z).gates[i]).args.length ≤ 2)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ z (i : Fin (C z).gates.length) a t, (s z).2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
    PolyTimeComputable fun z => pairEncode
      (BinArith.encWords (List.ofFn fun i =>
        BinArith.encWords (FakeObjects.table (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i)))
      (pairEncode
        (BinArith.encWords (List.ofFn fun v : Fin (inA z) =>
          List.ofFn (keyAt (C z) (s z) v false)))
        (BinArith.encWords (List.ofFn fun j : Fin (outLen z) =>
          pairEncode
            (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
              ((result z).getD j false)).1)
            (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
              ((result z).getD j false)).2)))) := by
  have ht := tables_poly hE₁ hE₂ width bound inputs description
    (fun z => BinArith.encWords (List.ofFn fun j => encodeNat (output z j))) coins
    hwidth hbound hinputs hdescription hcoins C s hshape hfan hkey hr₀ hr₁ hperm
  have hk := inputKeys_poly width bound inA inputs coins hwidth hbound hinA hcoins
    C s hinA_le hkey
  have houtsWord (z : List Bool) : pairSndD (description z) =
      BinArith.encWords (List.ofFn fun j => encodeNat (output z j)) := by
    rw [hshape z, pairSndD_pairEncode]
  have hp := outputPairs_poly width bound outLen inputs description coins result
    hwidth hbound houtLen hdescription hcoins hresult C s output houtsWord houtput_lt hkey
  exact ht.pairEncode (hk.pairEncode hp)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram
```

## ===== TCSlib/Cryptography/SecureComputation/Yao/HybridProof/FakeSimulatorFactory.lean (Lean, at 355a0288d56290e8c984228cbc1824187029e456) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed simulator contracts from supplied circuit and seed families

The factory consumes the existing data constructor once and returns simple word equations
on an abstract data value. This avoids downstream matching of its dependent constructor.

## Main definitions

None.

## Main results

* `exists_data`: supplied families admit data with the actual pointwise word equations.
* `exists_simulator`: one fixed uniform machine with actual run and ideal-sample equations.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (one fixed efficient simulator).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulatorFactory

open Complexity Turing BoolCircuit

variable
    (E₁ : List Bool → List Bool)
    (E₂ : List Bool → List Bool)
    (E₁_poly : PolyTimeComputable E₁)
    (E₂_poly : PolyTimeComputable E₂)
    (bound : PolyExpr)
    (inputs : PolyExpr)
    (inA : PolyExpr)
    (inB : PolyExpr)
    (outLen : PolyExpr)
    (gen : List Bool → List Bool)
    (gen_poly : PolyTimeComputable gen)
    (circuit : ∀ n, DAGCircuit (inputs.eval n))
    (output : ∀ n, Fin (outLen.eval n) → ℕ)
    (shape : ∀ n, gen (List.replicate n true) = pairEncode (circuit n).encode
    (BinArith.encWords (List.ofFn fun j => encodeNat (output n j))))
    (input_range : ∀ n, inA.eval n + inB.eval n ≤ inputs.eval n)
    (output_lt : ∀ n j, output n j < (circuit n).size)
    (fanin : ∀ n (i : Fin (circuit n).gates.length), ((circuit n).gates[i]).args.length ≤ 2)
    (seed : ∀ n, List Bool → GarbleSeed (circuit n) (Fin n → Bool)
    ((Fin n → Bool) × (Fin n → Bool)))
    (key : ∀ n r (v : ℕ), v < (circuit n).size → ∀ b,
    keyAt (circuit n) (seed n r) v b = fun t : Fin n =>
      r.getD ((b.toNat * bound.eval n + v) * n + t) false)
    (nonce₀ : ∀ n r (i : Fin (circuit n).gates.length) a t, ((seed n r).2.1 i a).1 t =
    r.getD (2 * bound.eval n * n +
      (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false)
    (nonce₁ : ∀ n r (i : Fin (circuit n).gates.length) a t, ((seed n r).2.1 i a).2 t =
    r.getD (2 * bound.eval n * n +
      (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false)
    (permutation : ∀ n r (i : Fin (circuit n).gates.length) a t,
    (seed n r).2.2 i a t = xor (a t) (r.getD (10 * bound.eval n * n + 2 * i + t) false))

include E₁_poly E₂_poly gen_poly shape input_range output_lt fanin key nonce₀ nonce₁ permutation

/-- The supplied algorithms, polynomial counts, circuit/output family and seed readers
admit one data value whose actual answer and message words are exactly those supplied.
The public data constructor and its word equations are consumed in a generic context.
[PS10, Theorem 163.7]
`∃ d : FakeSimulator.Data, (∀ n r, FakeSimulator.answersAt d n r = List.ofFn
(FakeObjects.activeAnswers (circuit n) (seed n r) (inA.eval n) (inB.eval n))) ∧ ∀ n r f,
FakeSimulator.messageAt d n r f = FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
(inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false)`.

**Proof sketch.** Construct the existing data value from the supplied fields. Apply each
of its pointwise constructor equations with every argument explicit. The resulting word
equations expose the dependent families together, without asking consumers to match them. -/
theorem exists_data :
    ∃ d : FakeSimulator.Data,
      (∀ n r, FakeSimulator.answersAt d n r =
        List.ofFn (FakeObjects.activeAnswers (circuit n) (seed n r)
          (inA.eval n) (inB.eval n))) ∧
      ∀ n r f, FakeSimulator.messageAt d n r f =
        FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
          (inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false) := by
  -- Step 1: construct the existing data value from the supplied fields, every argument named.
  refine ⟨FakeSimulator.Data.make
      (E₁ := E₁)
      (E₂ := E₂)
      (E₁_poly := E₁_poly)
      (E₂_poly := E₂_poly)
      (bound := bound)
      (inputs := inputs)
      (inA := inA)
      (inB := inB)
      (outLen := outLen)
      (gen := gen)
      (gen_poly := gen_poly)
      (circuit := circuit)
      (output := output)
      (shape := shape)
      (input_range := input_range)
      (output_lt := output_lt)
      (fanin := fanin)
      (seed := seed)
      (key := key)
      (nonce₀ := nonce₀)
      (nonce₁ := nonce₁)
      (permutation := permutation), ?_, ?_⟩
  -- Step 2: answer words, by the pointwise constructor equation with every argument explicit.
  · intro n r
    exact FakeSimulator.Data.make_answersAt
      (E₁ := E₁)
      (E₂ := E₂)
      (E₁_poly := E₁_poly)
      (E₂_poly := E₂_poly)
      (bound := bound)
      (inputs := inputs)
      (inA := inA)
      (inB := inB)
      (outLen := outLen)
      (gen := gen)
      (gen_poly := gen_poly)
      (circuit := circuit)
      (output := output)
      (shape := shape)
      (input_range := input_range)
      (output_lt := output_lt)
      (fanin := fanin)
      (seed := seed)
      (key := key)
      (nonce₀ := nonce₀)
      (nonce₁ := nonce₁)
      (permutation := permutation)
      n r
  -- Step 3: message words, by the pointwise constructor equation with every argument explicit.
  · intro n r f
    exact FakeSimulator.Data.make_messageAt
      (E₁ := E₁)
      (E₂ := E₂)
      (E₁_poly := E₁_poly)
      (E₂_poly := E₂_poly)
      (bound := bound)
      (inputs := inputs)
      (inA := inA)
      (inB := inB)
      (outLen := outLen)
      (gen := gen)
      (gen_poly := gen_poly)
      (circuit := circuit)
      (output := output)
      (shape := shape)
      (input_range := input_range)
      (output_lt := output_lt)
      (fanin := fanin)
      (seed := seed)
      (key := key)
      (nonce₀ := nonce₀)
      (nonce₁ := nonce₁)
      (permutation := permutation)
      n r f

/-- The supplied families admit one fixed uniform simulator with the prescribed coin
polynomial and exact raw-run and ideal-sampler equations in the original supplied families.
No downstream dependent-constructor matching or assumed leaf efficiency is needed.
[PS10, Theorem 163.7]
`∃ SB : NUPPT, SB.Uniform ∧ SB.coins = coins ∧ (∀ n y f r, SB.runAtL n (pairEncode y f) r =
(⟨List.replicate n true, pairEncode y (List.ofFn (FakeObjects.activeAnswers (circuit n) (seed n r)
(inA.eval n) (inB.eval n))), [], [FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
(inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false)]⟩ : View).encode) ∧ ∀ (F :
Functionality) n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (r : SB.Coins n),
F.idealB SB n x y r = pairEncode (⟨List.replicate n true, pairEncode (List.ofFn y) (List.ofFn
(FakeObjects.activeAnswers (circuit n) (seed n (List.ofFn r)) (inA.eval n) (inB.eval n))), [],
[FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n (List.ofFn r)) (inA.eval n)
(outLen.eval n) (output n) (fun j => (List.ofFn (F.f n x y).2).getD j false)]⟩ : View).encode
(List.ofFn (F.f n x y).1)`.

**Proof sketch.** Obtain the existing data value together with its two plain word equations.
Choose the previously proved uniform simulator on this data. Its coin contract supplies the
budget. Specialize its raw-run and ideal-sampler contracts, then replace the pointwise answer
and message words using the two supplied equations. This keeps the machine fixed before
any input, functionality, or distinguisher is introduced. -/
theorem exists_simulator (coins : PolyExpr) :
    ∃ SB : NUPPT, SB.Uniform ∧ SB.coins = coins ∧
      (∀ n y f r, SB.runAtL n (pairEncode y f) r =
        (⟨List.replicate n true, pairEncode y
          (List.ofFn (FakeObjects.activeAnswers (circuit n) (seed n r)
            (inA.eval n) (inB.eval n))), [],
          [FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
            (inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false)]⟩ : View).encode) ∧
      ∀ (F : Functionality) n (x : Fin (F.inA.eval n) → Bool)
        (y : Fin (F.inB.eval n) → Bool) (r : SB.Coins n),
        F.idealB SB n x y r =
          pairEncode
            (⟨List.replicate n true, pairEncode (List.ofFn y)
              (List.ofFn (FakeObjects.activeAnswers (circuit n) (seed n (List.ofFn r))
                (inA.eval n) (inB.eval n))), [],
              [FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n (List.ofFn r))
                (inA.eval n) (outLen.eval n) (output n)
                (fun j => (List.ofFn (F.f n x y).2).getD j false)]⟩ : View).encode
            (List.ofFn (F.f n x y).1) := by
  obtain ⟨d, ha, hm⟩ := exists_data
      (E₁ := E₁)
      (E₂ := E₂)
      (E₁_poly := E₁_poly)
      (E₂_poly := E₂_poly)
      (bound := bound)
      (inputs := inputs)
      (inA := inA)
      (inB := inB)
      (outLen := outLen)
      (gen := gen)
      (gen_poly := gen_poly)
      (circuit := circuit)
      (output := output)
      (shape := shape)
      (input_range := input_range)
      (output_lt := output_lt)
      (fanin := fanin)
      (seed := seed)
      (key := key)
      (nonce₀ := nonce₀)
      (nonce₁ := nonce₁)
      (permutation := permutation)
  refine ⟨FakeSimulator.simulator d coins, FakeSimulator.simulator_uniform d coins,
    FakeSimulator.simulator_coins d coins, ?_, ?_⟩
  · intro n y f r
    rw [FakeSimulator.simulator_runAtL, ha, hm]
  · intro F n x y r
    rw [FakeSimulator.idealB_eq, ha, hm]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulatorFactory
```

## ===== TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarblingProgram.lean (Lean, at 355a0288d56290e8c984228cbc1824187029e456) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AllTables
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Generic garbling programs from uniform circuit descriptions

The interface takes a circuit family, a polynomial-time description map, numeric/coin maps,
and a seed satisfying its key, row-nonce, and XOR-shift block equations. It does not refer
to any definition from `Yao.lean`.

## Main definitions

* `GarblingProgram.gatesWord`: the gate-record word extracted by the public decoder.

## Main results

* `GarblingProgram.tables_poly`: polynomial time for the actual encoded garbled tables.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (garbling the canonical uniform circuit).
* [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*,
  STOC 1990, pp. 503–513 (point-and-permute row order of the garbled tables).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

/-- The gate-record list extracted from a circuit-description pair:
`gatesWord description z = pairSndD (readCircuit (pairFstD (description z)))`. -/
def gatesWord (description : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairSndD (DescriptionDecoder.readCircuit (pairFstD (description z)))

/-- `gatesWord description z = pairSndD (readCircuit (pairFstD (description z)))`. -/
theorem gatesWord_eq (description : List Bool → List Bool) (z : List Bool) :
    gatesWord description z =
      pairSndD (DescriptionDecoder.readCircuit (pairFstD (description z))) := rfl

/-- Extracting the gate-record word is polynomial-time from a polynomial-time description.
`PolyTimeComputable (gatesWord description)`. -/
theorem gatesWord_poly {description : List Bool → List Bool}
    (hdescription : PolyTimeComputable description) : PolyTimeComputable (gatesWord description) :=
  polyTimeComputable_pairSndD.comp
    (DescriptionDecoder.readCircuit_poly.comp (polyTimeComputable_pairFstD.comp hdescription))

/-- A canonical description gives exactly its encoded gate-record list:
`gatesWord description z = encWords (C.gates.map gateRecord)`. -/
theorem gatesWord_description (description : List Bool → List Bool) (z : List Bool)
    {m : ℕ} (C : DAGCircuit m) (outs : List Bool)
    (hdescription : description z = pairEncode C.encode outs) :
    gatesWord description z = BinArith.encWords (C.gates.map DescriptionDecoder.gateRecord) := by
  rw [gatesWord_eq, hdescription, pairFstD_pairEncode,
    DescriptionDecoder.readCircuit_encode, pairSndD_pairEncode]

/-- The actual encoded garbled-table vector is polynomial-time from a polynomial-time
circuit-description pair, polynomial-time unary/coin maps, fan-in at most two, and the
supplied seed's key, row-nonce, and XOR-shift equations. [PS10, Protocol 162.6; BMR90]
`PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun i => BinArith.encWords (garbledTable
(nestedSpecial E₁ E₂ (width z)) (C z) (s z) i))`.

**Proof sketch.** Decode the description to its gate-record word and apply the total raw
all-table machine. At a canonical index, the public context-transport equation exposes the
selected gate record. Canonical list lookup supplies its kind and unary argument words.
The row-machine seed contract identifies every encrypted row, the table contract identifies
the enumerated table, and the outer word-vector contract identifies the complete table list.
No unproved indexed reconstruction hypothesis is left to the consumer. -/
theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs : List Bool → ℕ)
    (description outs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hshape : ∀ z, description z = pairEncode (C z).encode (outs z))
    (hfan : ∀ z (i : Fin (C z).gates.length), ((C z).gates[i]).args.length ≤ 2)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ z (i : Fin (C z).gates.length) a t, (s z).2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun i =>
      BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i)) := by
  let gates := gatesWord description
  have hgates : PolyTimeComputable gates := gatesWord_poly hdescription
  have hgs (z : List Bool) :
      gates z = BinArith.encWords ((C z).gates.map DescriptionDecoder.gateRecord) :=
    gatesWord_description description z (C z) (outs z) (hshape z)
  have hraw := AllTables.allTablesWord_poly hE₁ hE₂ hwidth hbound hinputs hgates hcoins
  refine hraw.congr fun z => ?_
  refine AllTables.allTablesWord_garbledTables E₁ E₂ width bound inputs gates coins
    DescriptionDecoder.gateRecord z (C z) (s z) (hgs z) ?_
  intro i
  -- Transport the indexed context before reading the selected canonical gate record.
  rw [AllTables.entryWord_pair]
  have hrecord : BinArith.getW (pairEncode (List.replicate i true) (gates z)) =
      DescriptionDecoder.gateRecord ((C z).gates[i]) := by
    rw [hgs z, BinArith.getW_pairEncode, List.length_replicate]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact i.isLt), List.getElem_map]
    rfl
  have hk : pairFstD (BinArith.getW (pairEncode (List.replicate i true) (gates z))) =
      ((C z).gates[i]).kind.encode := by
    rw [hrecord, DescriptionDecoder.gateRecord_eq, pairFstD_pairEncode]
  have ha : pairSndD (BinArith.getW (pairEncode (List.replicate i true) (gates z))) =
      BinArith.encWords (((C z).gates[i]).args.map fun v => List.replicate v true) := by
    rw [hrecord, DescriptionDecoder.gateRecord_eq, pairSndD_pairEncode]
  -- The seed equations supply the entire row-to-table semantic contract.
  refine TablesFromCoins.tableWord_garbledTable E₁ E₂ width bound inputs (fun _ => i)
    (fun v => pairFstD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
    (fun v => pairSndD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
    coins z (C z) (s z) i (hfan z i) ha ?_
  intro a
  exact RowFromCoins.rowWord_garbledRow E₁ E₂ width bound inputs (fun _ => i)
    (fun v => pairFstD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
    (fun v => pairSndD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
    coins z (C z) (s z) i a (hfan z i) rfl hk ha (hkey z) (hr₀ z i) (hr₁ z i) (hperm z i)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram
```

## ===== TCSlib/Cryptography/SecureComputation/Yao/HybridProof/RunWithHost.lean (Lean, at 355a0288d56290e8c984228cbc1824187029e456) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.Randomized.Repetition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A polynomial-time host for data-dependent gate evaluation

A gate traversal retains its input and a state consisting of the unprocessed gate records
and the current encoded vertex data. Its leaf routine receives the retained input, one gate
record and the vertex data, and returns the vertex data extended by the gate's result.
The host is generic in the gate records, the vertex-data encoding and the leaf routine.

Unlike the CVAL decider, this host returns the entire encoded value list and permits a
polynomial-time, input-dependent gate operation. It uses the registered state-loop host;
there is no new transition table.

## Main definitions

* `RunWithHost.step`: one gate-record traversal step.
* `RunWithHost.acc`: the test that no gate records remain.

## Main results

* `RunWithHost.orbit_eq`: the traversal state after a gate prefix.
* `RunWithHost.polyTimeComputable_runWith`: polynomial time under a polynomial state envelope.
* `RunWithHost.exists_machine`: one finite machine and a uniform polynomial time envelope.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, §6.1 (topologically ordered circuits).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (garbled evaluation).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost

open Complexity Turing BoolCircuit

/-- The traversal step sends `⟨x, ⟨records, values⟩⟩` to
`⟨tail records, F ⟨x, ⟨head records, values⟩⟩⟩`.
The outer retained input is maintained by the state-loop host.
`step F w = pairEncode (pairSndD (pairFstD (pairSndD w))) (F (pairEncode (pairFstD w) (pairEncode
(pairFstD (pairFstD (pairSndD w))) (pairSndD (pairSndD w)))))`. -/
def step (F : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD (pairSndD w)))
    (F (pairEncode (pairFstD w)
      (pairEncode (pairFstD (pairFstD (pairSndD w))) (pairSndD (pairSndD w)))))

/-- For every word `w`, `step F w` drops its first gate record and calls `F` on
`⟨fst w, ⟨head records, values⟩⟩`.
`step F w = pairEncode (pairSndD (pairFstD (pairSndD w))) (F (pairEncode (pairFstD w) (pairEncode
(pairFstD (pairFstD (pairSndD w))) (pairSndD (pairSndD w)))))`. -/
theorem step_eq (F : List Bool → List Bool) (w : List Bool) :
    step F w = pairEncode (pairSndD (pairFstD (pairSndD w)))
      (F (pairEncode (pairFstD w)
        (pairEncode (pairFstD (pairFstD (pairSndD w))) (pairSndD (pairSndD w))))) := rfl

/-- The traversal accepts exactly when its remaining record list is empty:
`acc w = decide (fst (snd w) = [])`. -/
def acc (w : List Bool) : Bool := decide (pairFstD (pairSndD w) = [])

/-- For every word `w`, `acc w = decide (pairFstD (pairSndD w) = [])`. -/
theorem acc_eq (w : List Bool) : acc w = decide (pairFstD (pairSndD w) = []) := rfl

/-- If `F` is polynomial-time, then `step F` is polynomial-time; it consists of
pair projections, two pairings and one call to `F`.
`PolyTimeComputable (step F)`. -/
theorem step_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (step F) :=
  ((polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
    (hF.comp (polyTimeComputable_pairFstD.pairEncode
      ((polyTimeComputable_pairFstD.comp
          (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))))

/-- The one-bit acceptance test `w ↦ [acc w]` is polynomial-time.
Reuses `StateLoop.MajLoop.acc_poly`.
`PolyTimeComputable fun w => [acc w]`. -/
theorem acc_poly : PolyTimeComputable fun w => [acc w] := by
  have hacc : ∀ w, acc w = Complexity.StateLoop.MajLoop.acc w := fun w =>
    (acc_eq w).trans (Complexity.StateLoop.MajLoop.acc_eq w).symm
  have hfun : (fun w => [acc w]) = fun w => [Complexity.StateLoop.MajLoop.acc w] :=
    funext fun w => congrArg (fun b : Bool => [b]) (hacc w)
  rw [hfun]
  exact Complexity.StateLoop.MajLoop.acc_poly

/-- After `i ≤ |gs x|` rounds, the state is the unprocessed gate suffix paired with
`valueCode x (runWith (f x) ((gs x).take i) (init x))`.

**Proof sketch.** At round zero the prefix is empty. At a successor round the head
of the remaining encoded list is the next gate record. The leaf contract appends
its computed value, and the append and singleton equations of `runWith` identify
the result with evaluation of the next prefix. -/
theorem orbit_eq {β : List Bool → Type} (gateCode : DAGGate → List Bool)
    (valueCode : ∀ x, List (β x) → List Bool) (gs : List Bool → List DAGGate)
    (init : ∀ x, List (β x)) (f : ∀ x, DAGGate → List (β x) → β x)
    (F : List Bool → List Bool)
    (hnext : ∀ x g vs,
      F (pairEncode x (pairEncode (gateCode g) (valueCode x vs))) =
        valueCode x (vs ++ [f x g vs])) (x : List Bool) :
    ∀ i, i ≤ (gs x).length →
      StateLoop.orbit
          (fun z => pairEncode (BinArith.encWords ((gs z).map gateCode)) (valueCode z (init z)))
          (step F) x i =
        pairEncode (BinArith.encWords (((gs x).drop i).map gateCode))
          (valueCode x (runWith (f x) ((gs x).take i) (init x))) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [StateLoop.orbit_zero, List.drop_zero, List.take_zero, runWith_nil]
  | succ i ih =>
    intro hi
    have hilt : i < (gs x).length := by omega
    rw [StateLoop.orbit_succ, ih (by omega), step_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [List.drop_eq_getElem_cons hilt, List.map_cons, BinArith.encWords_cons]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [hnext, List.take_succ_eq_append_getElem hilt, runWith_append, runWith_singleton]

/-- Evaluating `gs x` from `init x` and returning its `valueCode` is polynomial-time
when the encoded input maps and leaf routine are polynomial-time, the gate count
is at most `R |x|`, and every encoded prefix state has length at most `B |x|`.
The leaf receives `⟨x, ⟨gateCode g, valueCode x vs⟩⟩` and returns
`valueCode x (vs ++ [f x g vs])`. [PS10, Protocol 162.6]
`PolyTimeComputable fun x => valueCode x (runWith (f x) (gs x) (init x))`.

**Proof sketch.** Use the public state-loop host with the unprocessed gate records
and current vertex data as state. The orbit equation gives the caller's length
bound. Before the last round the encoded suffix contains a pair, so it is nonempty;
at the gate count it is empty. Thus the loop stops at exactly the gate count and
its second projection is the encoded result of `runWith`. -/
theorem polyTimeComputable_runWith {β : List Bool → Type} (gateCode : DAGGate → List Bool)
    (valueCode : ∀ x, List (β x) → List Bool) (gs : List Bool → List DAGGate)
    (init : ∀ x, List (β x)) (f : ∀ x, DAGGate → List (β x) → β x)
    {F : List Bool → List Bool}
    (hgs : PolyTimeComputable fun x => BinArith.encWords ((gs x).map gateCode))
    (hinit : PolyTimeComputable fun x => valueCode x (init x)) (hF : PolyTimeComputable F)
    (hnext : ∀ x g vs,
      F (pairEncode x (pairEncode (gateCode g) (valueCode x vs))) =
        valueCode x (vs ++ [f x g vs])) (R B : PolyExpr)
    (hN : ∀ x, (gs x).length ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ (gs x).length →
      (pairEncode (BinArith.encWords (((gs x).drop i).map gateCode))
        (valueCode x (runWith (f x) ((gs x).take i) (init x)))).length ≤ B.eval x.length) :
    PolyTimeComputable fun x => valueCode x (runWith (f x) (gs x) (init x)) := by
  have h := polyTimeComputable_stateFind (hgs.pairEncode hinit) (step_poly hF)
    acc_poly (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
    R B (fun x => (gs x).length) hN
    (fun x i hi => by
      rw [orbit_eq gateCode valueCode gs init f F hnext x i hi]
      exact hbound x i hi)
    (fun x i hi => by
      rw [orbit_eq gateCode valueCode gs init f F hnext x i hi.le, acc_eq]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]
      rw [List.drop_eq_getElem_cons hi, List.map_cons, BinArith.encWords_cons]
      apply decide_eq_false_iff_not.mpr
      exact pairEncode_ne_nil _ _)
    (fun x => by
      rw [orbit_eq gateCode valueCode gs init f F hnext x _ le_rfl, acc_eq]
      simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.drop_length,
        List.map_nil, BinArith.encWords_nil, decide_true])
  convert h using 1
  funext x
  rw [orbit_eq gateCode valueCode gs init f F hnext x _ le_rfl]
  simp only [Function.comp_apply, pairSndD_pairEncode, List.take_length]

/-- There is one clean evaluation machine `M` with a polynomial budget
`A (|arg| + 1)^d`, installing `valueCode arg (runWith (f arg) (gs arg) (init arg))`
and emitting nothing. At every time every work head of that same machine is
within the budget of the origin. The hypotheses are those of
`polyTimeComputable_runWith`. [PS10, Protocol 162.6]
`∃ (M : FinTM Bool) (A d : ℕ), ModuleHost.Clean M (fun x => valueCode x (runWith (f x) (gs x) (init
x))) (fun _ => []) (fun n => A * (n + 1) ^ d) ∧ ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
|(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤ (A *
(arg.length + 1) ^ d : ℕ)`.

The machine is obtained by applying the registered H14 clean-install contract to
the traversal's polynomial-time function; its head envelope is H14's `Clean.envelope`. -/
theorem exists_machine {β : List Bool → Type} (gateCode : DAGGate → List Bool)
    (valueCode : ∀ x, List (β x) → List Bool) (gs : List Bool → List DAGGate)
    (init : ∀ x, List (β x)) (f : ∀ x, DAGGate → List (β x) → β x)
    {F : List Bool → List Bool}
    (hgs : PolyTimeComputable fun x => BinArith.encWords ((gs x).map gateCode))
    (hinit : PolyTimeComputable fun x => valueCode x (init x)) (hF : PolyTimeComputable F)
    (hnext : ∀ x g vs,
      F (pairEncode x (pairEncode (gateCode g) (valueCode x vs))) =
        valueCode x (vs ++ [f x g vs])) (R B : PolyExpr)
    (hN : ∀ x, (gs x).length ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ (gs x).length →
      (pairEncode (BinArith.encWords (((gs x).drop i).map gateCode))
        (valueCode x (runWith (f x) ((gs x).take i) (init x)))).length ≤ B.eval x.length) :
    ∃ (M : FinTM Bool) (A d : ℕ),
      ModuleHost.Clean M (fun x => valueCode x (runWith (f x) (gs x) (init x)))
          (fun _ => []) (fun n => A * (n + 1) ^ d) ∧
        ∀ (x arg : List Bool) (v : ℕ) (j : Fin M.k),
          |(M.tm.runFrom
            (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
              (A * (arg.length + 1) ^ d : ℕ) := by
  obtain ⟨M, A, d, hM⟩ := ModuleHost.clean_install
    (polyTimeComputable_runWith gateCode valueCode gs init f hgs hinit hF hnext R B hN hbound)
  exact ⟨M, A, d, hM, fun x arg v j => hM.envelope x arg v j⟩

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.RunWithHost
```

## ===== TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SeedCoordinates.lean (Lean, at 355a0288d56290e8c984228cbc1824187029e456) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.NonceCoordinates

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coordinates of a garbling seed and its selected challenge

Existing product, sum, currying and Boolean-function equivalences expose a garbling seed
as its unchanged assignment permutation and one table of key/nonce values. The challenge
is one selected key and a padded vector of row nonces. No equality on coordinate values
is used; repeated actual values are allowed.

## Main definitions

* `SeedCoordinates.Permutations`, `Index`, `ChallengeIndex`: the coordinate types.
* `SeedCoordinates.seedEquiv`, `challengeEquiv`: the exact coordinate equivalences.

## Main results

* Exact forward and inverse coordinate readers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (fresh selected key and encryption coins).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates

open BoolCircuit

/-- The unchanged seed component is the family of assignment permutations at every gate.
`Permutations C = ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length →
Bool))`. -/
abbrev Permutations {m : ℕ} (C : DAGCircuit m) :=
  (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool)

/-- `Permutations C` is the dependent family of per-gate assignment permutations.
`Permutations C = ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length →
Bool))`. -/
theorem Permutations_eq {m : ℕ} (C : DAGCircuit m) :
    Permutations C =
      ((i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool)) := rfl

/-- A full seed coordinate is either a vertex/bit key label or a row nonce coordinate.
`Index C = ((Fin C.size × Bool) ⊕ NonceCoordinates.Index C)`. -/
abbrev Index {m : ℕ} (C : DAGCircuit m) :=
  (Fin C.size × Bool) ⊕ NonceCoordinates.Index C

/-- `Index C` is the sum of key labels and row-nonce coordinates.
`Index C = ((Fin C.size × Bool) ⊕ NonceCoordinates.Index C)`. -/
theorem Index_eq {m : ℕ} (C : DAGCircuit m) :
    Index C = ((Fin C.size × Bool) ⊕ NonceCoordinates.Index C) := rfl

/-- Challenge coordinates consist of one selected key slot and `q+1` padded nonce slots.
`ChallengeIndex q = (Unit ⊕ Fin (q + 1))`. -/
abbrev ChallengeIndex (q : ℕ) := Unit ⊕ Fin (q + 1)

/-- `ChallengeIndex q = Unit ⊕ Fin (q+1)`. -/
theorem ChallengeIndex_eq (q : ℕ) : ChallengeIndex q = (Unit ⊕ Fin (q + 1)) := rfl

/-- `Data C V` is the pair of the full two-key table and the full two-half nonce table.
`Data C V = ((Fin C.size → Bool → V) × ((i : Fin C.gates.length) → (Fin C.gates[i.val].args.length →
Bool) → V × V))`. -/
abbrev Data {m : ℕ} (C : DAGCircuit m) (V : Type) :=
  (Fin C.size → Bool → V) ×
    ((i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → V × V)

/-- `Data C V` is the product of its key and nonce function tables.
`Data C V = ((Fin C.size → Bool → V) × ((i : Fin C.gates.length) → (Fin C.gates[i.val].args.length →
Bool) → V × V))`. -/
theorem Data_eq {m : ℕ} (C : DAGCircuit m) (V : Type) :
    Data C V = ((Fin C.size → Bool → V) ×
      ((i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → V × V)) := rfl

/-- Existing currying, Boolean-function and sum-function equivalences identify the key/nonce
value tables with one coordinate function. No permutation distribution is involved.
`dataEquiv C V d = Sum.elim (fun label => d.1 label.1 label.2) (fun x => if x.2.2 then (d.2 x.1
x.2.1).2 else (d.2 x.1 x.2.1).1)`. -/
def dataEquiv {m : ℕ} (C : DAGCircuit m) (V : Type) : Data C V ≃ (Index C → V) :=
  let key := (Equiv.curry (Fin C.size) Bool V).symm
  let nonce : ((i : Fin C.gates.length) →
      (Fin C.gates[i.val].args.length → Bool) → V × V) ≃ (NonceCoordinates.Index C → V) :=
    ((Equiv.piCongrRight fun i => Equiv.piCongrRight fun _ :
        (Fin C.gates[i.val].args.length → Bool) => (Equiv.boolArrowEquivProd V).symm).trans
      (Equiv.piCongrRight fun i =>
        (Equiv.curry (Fin C.gates[i.val].args.length → Bool) Bool V).symm)).trans
      (Equiv.piCurry (fun (i : Fin C.gates.length)
        (_ : (Fin C.gates[i.val].args.length → Bool) × Bool) => V)).symm
  (key.prodCongr nonce).trans (Equiv.sumArrowEquivProdArrow _ _ V).symm

/-- The data-coordinate map reads the key table on key labels and the chosen nonce half.
`dataEquiv C V d = Sum.elim (fun label => d.1 label.1 label.2) (fun x => if x.2.2 then (d.2 x.1
x.2.1).2 else (d.2 x.1 x.2.1).1)`. -/
theorem dataEquiv_eq {m : ℕ} (C : DAGCircuit m) (V : Type) (d : Data C V) :
    dataEquiv C V d = Sum.elim (fun label => d.1 label.1 label.2)
      (fun x => if x.2.2 then (d.2 x.1 x.2.1).2 else (d.2 x.1 x.2.1).1) := rfl

/-- The inverse data-coordinate map restores both key choices and both nonce halves.
`(dataEquiv C V).symm f = ((fun v b => f (Sum.inl (v, b))), fun i a => (f (Sum.inr ⟨i, (a, false)⟩),
f (Sum.inr ⟨i, (a, true)⟩)))`. -/
theorem dataEquiv_symm {m : ℕ} (C : DAGCircuit m) (V : Type) (f : Index C → V) :
    (dataEquiv C V).symm f = ((fun v b => f (Sum.inl (v, b))),
      fun i a => (f (Sum.inr ⟨i, (a, false)⟩), f (Sum.inr ⟨i, (a, true)⟩))) := rfl

/-- The value-table equivalence retains any unchanged parameter `P`, such as actual XOR
shifts and unused tape coordinates. No uniformity of a derived permutation is assumed.
`paramEquiv C V P (p, d) = (p, dataEquiv C V d)`. -/
def paramEquiv {m : ℕ} (C : DAGCircuit m) (V P : Type) :
    P × Data C V ≃ P × (Index C → V) := (Equiv.refl P).prodCongr (dataEquiv C V)

/-- `paramEquiv` retains `p` and converts only the key/nonce data table.
`paramEquiv C V P (p, d) = (p, dataEquiv C V d)`. -/
theorem paramEquiv_eq {m : ℕ} (C : DAGCircuit m) (V P : Type) (p : P) (d : Data C V) :
    paramEquiv C V P (p, d) = (p, dataEquiv C V d) := rfl

/-- The inverse parameterized map retains `p` and restores only its data table.
`(paramEquiv C V P).symm (p, f) = (p, (dataEquiv C V).symm f)`. -/
theorem paramEquiv_symm {m : ℕ} (C : DAGCircuit m) (V P : Type) (p : P) (f : Index C → V) :
    (paramEquiv C V P).symm (p, f) = (p, (dataEquiv C V).symm f) := rfl

/-- A full abstract garbling seed is equivalent to its permutation family and key/nonce
coordinate table. This auxiliary equivalence makes no claim that concrete XOR-shift tapes
induce uniform samples over all permutations.
`seedEquiv C V s = (s.2.2, Sum.elim (fun label => s.1 label.1 label.2) (fun x => if x.2.2 then
(s.2.1 x.1 x.2.1).2 else (s.2.1 x.1 x.2.1).1))`. -/
def seedEquiv {m : ℕ} (C : DAGCircuit m) (V : Type) :
    GarbleSeed C V (V × V) ≃ Permutations C × (Index C → V) :=
  ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _)).trans
    ((Equiv.refl _).prodCongr (dataEquiv C V))

/-- `seedEquiv` retains the permutations and reads key labels or first/second row nonces.
`seedEquiv C V s = (s.2.2, Sum.elim (fun label => s.1 label.1 label.2) (fun x => if x.2.2 then
(s.2.1 x.1 x.2.1).2 else (s.2.1 x.1 x.2.1).1))`. -/
theorem seedEquiv_eq {m : ℕ} (C : DAGCircuit m) (V : Type) (s : GarbleSeed C V (V × V)) :
    seedEquiv C V s = (s.2.2, Sum.elim (fun label => s.1 label.1 label.2)
      (fun x => if x.2.2 then (s.2.1 x.1 x.2.1).2 else (s.2.1 x.1 x.2.1).1)) := rfl

/-- The coordinate permutation family is exactly the original seed's permutation family.
`(seedEquiv C V s).1 = s.2.2`. -/
theorem seedEquiv_perm {m : ℕ} (C : DAGCircuit m) (V : Type) (s : GarbleSeed C V (V × V)) :
    (seedEquiv C V s).1 = s.2.2 := rfl

/-- A key coordinate reads its original vertex/bit key.
`(seedEquiv C V s).2 (Sum.inl (v, b)) = s.1 v b`. -/
theorem seedEquiv_key {m : ℕ} (C : DAGCircuit m) (V : Type) (s : GarbleSeed C V (V × V))
    (v : Fin C.size) (b : Bool) : (seedEquiv C V s).2 (Sum.inl (v, b)) = s.1 v b := rfl

/-- A nonce coordinate reads the first half for `false` and the second half for `true`.
`(seedEquiv C V s).2 (Sum.inr ⟨i, (a, half)⟩) = if half then (s.2.1 i a).2 else (s.2.1 i a).1`. -/
theorem seedEquiv_nonce {m : ℕ} (C : DAGCircuit m) (V : Type) (s : GarbleSeed C V (V × V))
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) (half : Bool) :
    (seedEquiv C V s).2 (Sum.inr ⟨i, (a, half)⟩) =
      if half then (s.2.1 i a).2 else (s.2.1 i a).1 := rfl

/-- The inverse coordinate map restores the two key choices, both nonce halves, and the
unchanged permutation family.
`(seedEquiv C V).symm (p, f) = ((fun v b => f (Sum.inl (v, b))), ((fun i a => (f (Sum.inr ⟨i, (a,
false)⟩), f (Sum.inr ⟨i, (a, true)⟩))), p))`. -/
theorem seedEquiv_symm {m : ℕ} (C : DAGCircuit m) (V : Type)
    (p : Permutations C) (f : Index C → V) :
    (seedEquiv C V).symm (p, f) =
      ((fun v b => f (Sum.inl (v, b))),
        ((fun i a => (f (Sum.inr ⟨i, (a, false)⟩), f (Sum.inr ⟨i, (a, true)⟩))), p)) := rfl

/-- A selected key and its padded nonce vector are one table on the sum of challenge slots.
`challengeEquiv q V (k, r) = Sum.elim (fun _ => k) r`. -/
def challengeEquiv (q : ℕ) (V : Type) :
    V × (Fin (q + 1) → V) ≃ (ChallengeIndex q → V) :=
  (((Equiv.funUnique Unit V).symm).prodCongr (Equiv.refl _)).trans
    (Equiv.sumArrowEquivProdArrow Unit (Fin (q + 1)) V).symm

/-- `challengeEquiv q V (k,r)` is `Sum.elim (fun _ => k) r`. -/
theorem challengeEquiv_eq (q : ℕ) (V : Type) (k : V) (r : Fin (q + 1) → V) :
    challengeEquiv q V (k, r) = Sum.elim (fun _ => k) r := rfl

/-- The inverse challenge-coordinate map reads the key slot and all padded nonce slots.
`(challengeEquiv q V).symm f = (f (Sum.inl ()), fun j => f (Sum.inr j))`. -/
theorem challengeEquiv_symm (q : ℕ) (V : Type) (f : ChallengeIndex q → V) :
    (challengeEquiv q V).symm f = (f (Sum.inl ()), fun j => f (Sum.inr j)) := rfl

/-- Pick the single key slot at `(u,true)`, or the selected nonce slot given by the nonce
coordinate map. The map depends on the row permutation and never on coordinate values.
`pick C rows perm u q x = Sum.elim (fun label => if label = (u, true) then some (Sum.inl () :
ChallengeIndex q) else none) (fun nonce => (NonceCoordinates.pick C rows perm u.val q nonce).map
Sum.inr) x`. -/
noncomputable def pick {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : Permutations C) (u : Fin C.size) (q : ℕ) (x : Index C) :
    Option (ChallengeIndex q) :=
  Sum.elim (fun label => if label = (u, true) then some (Sum.inl () : ChallengeIndex q) else none)
    (fun nonce => (NonceCoordinates.pick C rows perm u.val q nonce).map Sum.inr) x

/-- `pick` selects the key challenge at `(u,true)` and delegates nonce coordinates to the
nonce-slot map.
`pick C rows perm u q x = Sum.elim (fun label => if label = (u, true) then some (Sum.inl () :
ChallengeIndex q) else none) (fun nonce => (NonceCoordinates.pick C rows perm u.val q nonce).map
Sum.inr) x`. -/
theorem pick_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : Permutations C) (u : Fin C.size) (q : ℕ) (x : Index C) :
    pick C rows perm u q x =
      Sum.elim
        (fun label => if label = (u, true) then some (Sum.inl () : ChallengeIndex q) else none)
        (fun nonce => (NonceCoordinates.pick C rows perm u.val q nonce).map Sum.inr) x := rfl

/-- Place the selected key at `(u,true)` and each used nonce slot at its selected row half.
`place C rows perm u q j = Sum.elim (fun _ => some (Sum.inl (u, true) : Index C)) (fun nonce =>
(NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr) j`. -/
def place {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : Permutations C) (u : Fin C.size) (q : ℕ) (j : ChallengeIndex q) : Option (Index C) :=
  Sum.elim (fun _ => some (Sum.inl (u, true) : Index C))
    (fun nonce => (NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr) j

/-- `place` retains the distinction between the key challenge and padded nonce challenges.
`place C rows perm u q j = Sum.elim (fun _ => some (Sum.inl (u, true) : Index C)) (fun nonce =>
(NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr) j`. -/
theorem place_eq {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : Permutations C) (u : Fin C.size) (q : ℕ) (j : ChallengeIndex q) :
    place C rows perm u q j =
      Sum.elim (fun _ => some (Sum.inl (u, true) : Index C))
        (fun nonce => (NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr) j := rfl

/-- Full key/nonce picks and placements are exact partial inverses. The key and nonce
summands are disjoint, and nonce padding remains unmatched.
`pick C rows perm u q x = some j ↔ place C rows perm u q j = some x`.

**Proof sketch.** In the key summand there is one matching vertex/bit coordinate and one
challenge slot. Mixed summands cannot match. Within the nonce summand, injectivity of the
sum constructor reduces both directions to the existing nonce-coordinate inverse contract. -/
theorem pick_iff_place {m : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (perm : Permutations C) (u : Fin C.size) (q : ℕ)
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i) (hrows : ∀ i, (rows i).Nodup)
    (x : Index C) (j : ChallengeIndex q) :
    pick C rows perm u q x = some j ↔ place C rows perm u q j = some x := by
  cases x with
  | inl label =>
    cases j with
    | inl keySlot =>
      -- Step 1: key summand. The only matching pair is the coordinate `(u, true)` and the single
      -- key slot.
      cases keySlot
      rw [pick_eq, place_eq]
      change (if label = (u, true) then some (Sum.inl () : ChallengeIndex q) else none) =
        some (Sum.inl () : ChallengeIndex q) ↔
        some (Sum.inl (u, true) : Index C) = some (Sum.inl label : Index C)
      by_cases h : label = (u, true)
      · subst label
        constructor
        · intro _; rfl
        · intro _; exact if_pos rfl
      · constructor
        · intro h'
          rw [if_neg h] at h'
          cases h'
        · intro h'
          exact (h (Sum.inl.inj (Option.some.inj h')).symm).elim
    | inr nonce =>
      -- Step 2: mixed summands cannot match. A key label never picks a nonce slot, and `place`
      -- sends nonce slots only to nonce coordinates.
      rw [pick_eq, place_eq]
      change (if label = (u, true) then some (Sum.inl () : ChallengeIndex q) else none) =
        some (Sum.inr nonce : ChallengeIndex q) ↔
        (NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr =
          some (Sum.inl label : Index C)
      constructor
      · intro h
        by_cases hc : label = (u, true)
        · rw [if_pos hc] at h; cases h
        · rw [if_neg hc] at h; cases h
      · intro h
        obtain ⟨_, _, heq⟩ := Option.map_eq_some_iff.mp h
        cases heq
  | inr coordinate =>
    cases j with
    | inl keySlot =>
      -- Step 3: mixed summands cannot match. A nonce coordinate never picks the key slot, and
      -- `place` sends the key slot to a key label.
      cases keySlot
      rw [pick_eq, place_eq]
      change (NonceCoordinates.pick C rows perm u.val q coordinate).map Sum.inr =
        some (Sum.inl () : ChallengeIndex q) ↔
          some (Sum.inl (u, true) : Index C) = some (Sum.inr coordinate : Index C)
      constructor
      · intro h
        obtain ⟨_, _, heq⟩ := Option.map_eq_some_iff.mp h
        cases heq
      · intro h; cases h
    | inr nonce =>
      -- Step 4: nonce summand. Injectivity of `Sum.inr` reduces both directions to the
      -- nonce-coordinate inverse contract `NonceCoordinates.pick_iff_place`.
      rw [pick_eq, place_eq]
      change (NonceCoordinates.pick C rows perm u.val q coordinate).map Sum.inr =
        some (Sum.inr nonce : ChallengeIndex q) ↔
          (NonceCoordinates.place C rows perm u.val q nonce).map Sum.inr =
            some (Sum.inr coordinate : Index C)
      constructor
      · intro h
        obtain ⟨j, hp, heq⟩ := Option.map_eq_some_iff.mp h
        have hj : j = nonce := Sum.inr.inj heq
        subst j
        exact Option.map_eq_some_iff.mpr ⟨coordinate,
          (NonceCoordinates.pick_iff_place C rows perm u.val q hargs hcomplete hrows _ _).mp hp,
          rfl⟩
      · intro h
        obtain ⟨x, hp, heq⟩ := Option.map_eq_some_iff.mp h
        have hx : x = coordinate := Sum.inr.inj heq
        subst x
        exact Option.map_eq_some_iff.mpr ⟨nonce,
          (NonceCoordinates.pick_iff_place C rows perm u.val q hargs hcomplete hrows _ _).mpr hp,
          rfl⟩

/-- The seed coordinate map is its unchanged permutation paired with the data-coordinate map.
`seedEquiv C V s = (s.2.2, dataEquiv C V (s.1, s.2.1))`. -/
theorem seedEquiv_eq_data {m : ℕ} (C : DAGCircuit m) (V : Type)
    (s : GarbleSeed C V (V × V)) :
    seedEquiv C V s = (s.2.2, dataEquiv C V (s.1, s.2.1)) := rfl

/-- Filling the selected key and nonce vector is exactly the value-coordinate replacement
prescribed by `pick`. This pointwise identity holds at every value, including collisions,
and for arbitrary unused padding; no distribution or permutation-uniformity assumption occurs.
`dataEquiv C V ((SelectedSeed.fill C rows s u q k r).1, (SelectedSeed.fill C rows s u q k r).2.1) =
fun x => (pick C rows s.2.2 u q x).elim (dataEquiv C V (s.1, s.2.1) x) (challengeEquiv q V (k, r))`.

**Proof sketch.** At key coordinates the filled-key reader changes just `(u,true)`, matching
the single key slot. At nonce coordinates the nonce-coordinate read contract gives precisely
the picked challenge value or the retained old value. The challenge sum map reads the key
in its left summand and the nonce vector in its right summand. -/
theorem dataEquiv_fill {m : ℕ} (C : DAGCircuit m) (V : Type)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C V (V × V)) (u : Fin C.size) (q : ℕ) (k : V)
    (r : Fin (q + 1) → V) :
    dataEquiv C V ((SelectedSeed.fill C rows s u q k r).1,
      (SelectedSeed.fill C rows s u q k r).2.1) =
        fun x => (pick C rows s.2.2 u q x).elim (dataEquiv C V (s.1, s.2.1) x)
          (challengeEquiv q V (k, r)) := by
  funext x
  cases x with
  | inl label =>
    rcases label with ⟨v, b⟩
    simp only [dataEquiv_eq, pick_eq, Sum.elim_inl, SelectedSeed.fill_key,
      challengeEquiv_eq, Prod.mk.injEq]
    by_cases h : v = u ∧ b = true
    · simp only [h, and_self, ite_true, Option.elim_some, Sum.elim_inl]
    · simp only [h, ite_false, Option.elim_none]
  | inr coordinate =>
    rcases coordinate with ⟨i, a, half⟩
    simp only [dataEquiv_eq, Sum.elim_inr, SelectedSeed.fill_nonce]
    rw [NonceCoordinates.nonce_read]
    simp only [pick_eq, challengeEquiv_eq, Sum.elim_inr]
    cases h : NonceCoordinates.pick C rows s.2.2 u.val q ⟨i, (a, half)⟩ with
    | none => simp only [Option.map_none, Option.elim_none]
    | some j => simp only [Option.map_some, Option.elim_some, Sum.elim_inr]

/-- The complete filled abstract seed retains its permutation and performs exactly the
partial replacement of its key/nonce value coordinates.
`seedEquiv C V (SelectedSeed.fill C rows s u q k r) = (s.2.2, fun x => (pick C rows s.2.2 u q
x).elim (dataEquiv C V (s.1, s.2.1) x) (challengeEquiv q V (k, r)))`. -/
theorem seedEquiv_fill {m : ℕ} (C : DAGCircuit m) (V : Type)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C V (V × V)) (u : Fin C.size) (q : ℕ) (k : V)
    (r : Fin (q + 1) → V) :
    seedEquiv C V (SelectedSeed.fill C rows s u q k r) =
      (s.2.2, fun x => (pick C rows s.2.2 u q x).elim (dataEquiv C V (s.1, s.2.1) x)
        (challengeEquiv q V (k, r))) :=
  (seedEquiv_eq_data C V _).trans (Prod.ext
    (funext fun i => SelectedSeed.fill_perm C rows s u q k r i)
    (dataEquiv_fill C V rows s u q k r))

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SeedCoordinates
```

## ===== TCSlib/Cryptography/SecureComputation/Yao/HybridProof/SelectedLaw.lean (Lean, at 355a0288d56290e8c984228cbc1824187029e456) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoordinateSwap
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SeedCoordinates
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fresh selected coordinates in the actual tape distribution

## Main definitions

None.

## Main results

* `acceptProb_fill`: filling the selected key and row nonces preserves the actual tape law.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (fixing all other randomness in the gate hybrid).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedLaw

open BoolCircuit TCSlib.Cryptography

variable {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
  (hA : ∀ i : Fin C.gates.length, (C.gates[i.val]).args.length ≤ 2) (hS : C.size ≤ S)
  (seed : List Bool → GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (hK : ∀ q (w : Fin C.size) b (t : Fin n),
    (seed q).1 w b t = q.getD ((b.toNat * S + w) * n + t) false)
  (hR₀ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool)
      (t : Fin n),
    ((seed q).2.1 i a).1 t = q.getD (2 * S * n + (4 * i +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false)
  (hR₁ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool)
      (t : Fin n),
    ((seed q).2.1 i a).2 t = q.getD (2 * S * n + (4 * i +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false)
  (hP : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i.val]).args.length → Bool)
      (t : Fin (C.gates[i.val]).args.length),
    (seed q).2.2 i a t = xor (a t) (q.getD (10 * S * n + 2 * i + t) false))


include hA hS hK hR₀ hR₁ hP

/-- For a seed with the four actual addressed tape readers, independently replacing one
inactive key and every matched row nonce preserves every sampler's acceptance probability.
All shifts and unused padded coordinates retain their actual distribution; there is no
uniformity assumption on the derived assignment permutations. No occurrence-capacity or
key-value-distinctness premise is required. [PS10, Theorem 163.7]
`acceptProb (fun z : (Fin (10 * S * n + 2 * S) → Bool) × ((Fin n → Bool) × (Fin (q + 1) → Fin n →
Bool)) => X (SelectedSeed.fill C rows (seed (List.ofFn z.1)) u q z.2.1 z.2.2)) D = acceptProb (fun r
: Fin (10 * S * n + 2 * S) → Bool => X (seed (List.ofFn r))) D`.

**Proof sketch.** Split the complete tape into its retained shift/unused-block parameter
and independent actual key/nonce values. Convert the value table and challenge into their
existing coordinate types. The seed's inverse reader identifies the original sample with
these coordinates, and the filled-seed reader identifies replacement with the matched
coordinate exchange. Apply that exchange's proved uniform acceptance law and transport
back through the two coordinate equivalences. -/
theorem acceptProb_fill
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (u : Fin C.size) (q : ℕ)
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i) (hrows : ∀ i, (rows i).Nodup)
    {γ κ : Type*} [Fintype κ]
    (X : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)) → γ)
    (D : γ → κ → Bool) :
    acceptProb
      (fun z : (Fin (10 * S * n + 2 * S) → Bool) ×
          ((Fin n → Bool) × (Fin (q + 1) → Fin n → Bool)) =>
        X (SelectedSeed.fill C rows (seed (List.ofFn z.1)) u q z.2.1 z.2.2)) D =
      acceptProb (fun r : Fin (10 * S * n + 2 * S) → Bool => X (seed (List.ofFn r))) D := by
  classical
  -- Step 1: `e` splits the tape into the retained shift/unused-block parameter and the actual
  -- key/nonce values in their coordinate type; `c` converts the challenge likewise.
  let P := TapeValues.Rest C S n hA hS
  let V := Fin n → Bool
  let e := (TapeValues.equiv C S n hA hS).trans (SeedCoordinates.paramEquiv C V P)
  let c := SeedCoordinates.challengeEquiv q V
  letI : Fintype (P × (SeedCoordinates.Index C → V)) :=
    Fintype.ofEquiv (Fin (10 * S * n + 2 * S) → Bool) e
  letI : Fintype (SeedCoordinates.ChallengeIndex q → V) :=
    Fintype.ofEquiv (V × (Fin (q + 1) → V)) c
  letI : Nonempty (SeedCoordinates.ChallengeIndex q → V) :=
    ⟨c ((fun _ => false), fun _ _ => false)⟩
  -- Step 2: each parameter's permutations give the matched coordinate exchange `pick`/`place`.
  let perm : P → SeedCoordinates.Permutations C := TapeValues.permutation C S n hA hS
  let pick := fun p : P => SeedCoordinates.pick C rows (perm p) u q
  let place := fun p : P => SeedCoordinates.place C rows (perm p) u q
  have hmatch : ∀ p i j, pick p i = some j ↔ place p j = some i :=
    fun p => SeedCoordinates.pick_iff_place C rows (perm p) u q hargs hcomplete hrows
  -- Step 3: the seed's inverse reader identifies the original sample with these coordinates.
  have hSeed (z : P × (SeedCoordinates.Index C → V)) :
      seed (List.ofFn (e.symm z)) =
        (SeedCoordinates.seedEquiv C V).symm (perm z.1, z.2) := by
    rcases z with ⟨p, full⟩
    change seed (List.ofFn ((TapeValues.equiv C S n hA hS).symm
      ((SeedCoordinates.paramEquiv C V P).symm (p, full)))) = _
    rw [SeedCoordinates.paramEquiv_symm,
      TapeValues.seed_on_inverse C S n hA hS seed hK hR₀ hR₁ hP]
    rw [SeedCoordinates.seedEquiv_symm, SeedCoordinates.dataEquiv_symm]
  -- Step 4: the filled-seed reader identifies the replacement with the matched exchange.
  have hFilled (z : P × (SeedCoordinates.Index C → V))
      (t : SeedCoordinates.ChallengeIndex q → V) :
      SelectedSeed.fill C rows (seed (List.ofFn (e.symm z))) u q
          (c.symm t).1 (c.symm t).2 =
        (SeedCoordinates.seedEquiv C V).symm
          (perm (CoordinateSwap.swap pick place (z, t)).1.1,
            (CoordinateSwap.swap pick place (z, t)).1.2) := by
    apply (SeedCoordinates.seedEquiv C V).injective
    have hs := (congrArg (SeedCoordinates.seedEquiv C V) (hSeed z)).trans
      (Equiv.apply_symm_apply (SeedCoordinates.seedEquiv C V) (perm z.1, z.2))
    rw [SeedCoordinates.seedEquiv_eq_data] at hs
    have hp := congrArg Prod.fst hs
    have hd := congrArg Prod.snd hs
    change (seed (List.ofFn (e.symm z))).2.2 = perm z.1 at hp
    change SeedCoordinates.dataEquiv C V
      ((seed (List.ofFn (e.symm z))).1, (seed (List.ofFn (e.symm z))).2.1) = z.2 at hd
    have hc : SeedCoordinates.challengeEquiv q V ((c.symm t).1, (c.symm t).2) = t :=
      Equiv.apply_symm_apply c t
    rw [Equiv.apply_symm_apply, SeedCoordinates.seedEquiv_fill, hp, hd, hc,
      CoordinateSwap.swap_eq]
  -- Step 5: transport the actual sampler through the tape equivalence `e`.
  let Z := fun z : P × (SeedCoordinates.Index C → V) =>
    X ((SeedCoordinates.seedEquiv C V).symm (perm z.1, z.2))
  have hStart : acceptProb Z D =
      acceptProb (fun r : Fin (10 * S * n + 2 * S) → Bool => X (seed (List.ofFn r))) D := by
    have h := acceptProb_comp_equiv e.symm
      (fun r : Fin (10 * S * n + 2 * S) → Bool => X (seed (List.ofFn r))) D
    have hf : (fun z : P × (SeedCoordinates.Index C → V) =>
        X (seed (List.ofFn (e.symm z)))) = Z :=
      funext fun z => congrArg X (hSeed z)
    rw [hf] at h
    exact h
  -- Step 6: pointwise, the filled sampler is the exchanged one under `e.prodCongr c`.
  have hPoint (z : (Fin (10 * S * n + 2 * S) → Bool) ×
      (V × (Fin (q + 1) → V))) :
      X (SelectedSeed.fill C rows (seed (List.ofFn z.1)) u q z.2.1 z.2.2) =
        Z (CoordinateSwap.swap pick place ((e.prodCongr c) z)).1 := by
    have h := congrArg X (hFilled (e z.1) (c z.2))
    rw [Equiv.symm_apply_apply e z.1, Equiv.symm_apply_apply c z.2] at h
    change X (SelectedSeed.fill C rows (seed (List.ofFn z.1)) u q z.2.1 z.2.2) =
      X ((SeedCoordinates.seedEquiv C V).symm
        (perm (CoordinateSwap.swap pick place (e z.1, c z.2)).1.1,
          (CoordinateSwap.swap pick place (e z.1, c z.2)).1.2))
    exact h
  -- Step 7: transport through `e.prodCongr c`, apply the exchange's proved uniform acceptance
  -- law `CoordinateSwap.acceptProb_swap`, and return to the actual tape by Step 5.
  have hTransport := acceptProb_comp_equiv (e.prodCongr c)
    (fun z : (P × (SeedCoordinates.Index C → V)) ×
        (SeedCoordinates.ChallengeIndex q → V) => Z (CoordinateSwap.swap pick place z).1) D
  have hf : (fun z : (Fin (10 * S * n + 2 * S) → Bool) ×
      (V × (Fin (q + 1) → V)) =>
      X (SelectedSeed.fill C rows (seed (List.ofFn z.1)) u q z.2.1 z.2.2)) =
    (fun z => Z (CoordinateSwap.swap pick place ((e.prodCongr c) z)).1) := funext hPoint
  rw [hf]
  exact hTransport.trans ((CoordinateSwap.acceptProb_swap pick place hmatch Z D).trans hStart)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedLaw
```

## ===== TCSlib/Complexity/Randomized/Build/StringLoops.lean (Lean, at 355a0288d56290e8c984228cbc1824187029e456) =====

```lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Bool.Count
import TCSlib.Complexity.Randomized.Build.StateLoop
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop
import TCSlib.Complexity.ClassP.BinaryArith.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# String loops: majority, pairwise xor, equality test and block map

The four string functions of `TCSlib.Complexity.Randomized.Repetition` —
`Complexity.polyTimeComputable_majority` (the vote of [PS10, Algorithm 89.6]),
`Complexity.polyTimeComputable_pairXor` (the one-time pad of [PS10, Algorithms 92.1 and 99.1]
and the mask of [PS10, Algorithm 104.3]), `Complexity.polyTimeComputable_pairEq` (the test
`f(z_i) = y` of [PS10, Algorithm 38.5]) and `Complexity.polyTimeComputable_blockMap` (the
blockwise evaluation of `prodFun` in [PS10, Theorem 35.1]) — are **state loops** in the sense
of `TCSlib.Complexity.Randomized.Build.StateLoop`: a state word `⟨z, s⟩` retains the input `z`,
the state `s` consumes the input one bit (or one block) per round, a test `acc` fires for the
first time when the input is exhausted, and `out` reads the answer off the final state.

This file supplies, for each of the four, the loop data (`start`, `step`, `acc`, `out`, the
number of rounds), the polynomial-time proofs of the data, the closed form of the orbit, its
length bound and the values of `acc` and `out` along it:

* `Complexity.StateLoop.MajLoop` — state `⟨rest, ⟨1^{#true}, 1^{#false}⟩⟩`, one bit per round;
* `Complexity.StateLoop.XorLoop` — state `⟨a', ⟨b', c⟩⟩`, one xor bit appended per round;
* `Complexity.StateLoop.EqLoop` — state `⟨a', ⟨b', flag⟩⟩`, the flag recording a mismatch;
* `Complexity.StateLoop.BlockMapLoop` — state `⟨rest, c⟩`, one block of `b(|fst z|)` bits per
  round, the accumulator extended by `g` of the block.

The assembly through `Complexity.polyTimeComputable_iterateFind` (the public state-loop form
`Complexity.polyTimeComputable_stateFind`) and the four public theorems live in
`TCSlib.Complexity.Randomized.Repetition`.

## Main definitions

* `Complexity.StateLoop.MajLoop`, `Complexity.StateLoop.XorLoop`, `Complexity.StateLoop.EqLoop`,
  `Complexity.StateLoop.BlockMapLoop` — the state-loop data of the four string functions.

## Main results

* The `orbit_eq` closed forms, `orbit_length_le` bounds, `acc_orbit_false`/`acc_orbit_true`
  values and `out_orbit` identities of the four loops; `Complexity.StateLoop.EqLoop.verdict_eq`
  (equal lengths and equal prefixes is equality).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Algorithms 89.6, 92.1, 99.1 and 104.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines; §2.2, the class FP.)
-/

namespace Complexity.StateLoop

open Turing

/-! ### `majority`: consume the word, counting `true`s and `false`s in unary -/

namespace MajLoop

/-- The initial state `⟨w, ⟨[], []⟩⟩`: the whole word remains, both counters empty. -/
def start (w : List Bool) : List Bool := pairEncode w (pairEncode [] [])

/-- The initial state is `start w = ⟨w, ⟨[], []⟩⟩`. -/
theorem start_eq (w : List Bool) : start w = pairEncode w (pairEncode [] []) :=
  rfl

/-- The step on `⟨w, ⟨rest, ⟨t, f⟩⟩⟩`: drop the first bit of `rest` and append a token to the
counter of its value. -/
def step (v : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD v)).tail
    (if (pairFstD (pairSndD v)).headD false then
      pairEncode (true :: pairFstD (pairSndD (pairSndD v))) (pairSndD (pairSndD (pairSndD v)))
    else pairEncode (pairFstD (pairSndD (pairSndD v))) (true :: pairSndD (pairSndD (pairSndD v))))

/-- The step on `v = ⟨w, ⟨rest, ⟨t, f⟩⟩⟩` is `⟨rest.tail, ⟨true :: t, f⟩⟩` if the head bit of
`rest` is `true` (`false` on the empty word), and `⟨rest.tail, ⟨t, true :: f⟩⟩` otherwise. -/
theorem step_eq (v : List Bool) :
    step v =
      pairEncode (pairFstD (pairSndD v)).tail
        (if (pairFstD (pairSndD v)).headD false then
          pairEncode (true :: pairFstD (pairSndD (pairSndD v))) (pairSndD (pairSndD (pairSndD v)))
        else
          pairEncode (pairFstD (pairSndD (pairSndD v)))
            (true :: pairSndD (pairSndD (pairSndD v)))) :=
  rfl

/-- The acceptance test: the remaining word is empty. -/
def acc (v : List Bool) : Bool := decide (pairFstD (pairSndD v) = [])

/-- The acceptance test is `acc v = decide (rest = [])` for `v = ⟨w, ⟨rest, ⟨t, f⟩⟩⟩`. -/
theorem acc_eq (v : List Bool) : acc v = decide (pairFstD (pairSndD v) = []) :=
  rfl

/-- The output: the verdict `#false + 1 ≤ #true`, i.e. a strict majority of `true`. -/
def out (v : List Bool) : List Bool :=
  [decide ((true :: pairSndD (pairSndD (pairSndD v))).length ≤
    (pairFstD (pairSndD (pairSndD v))).length)]

/-- The output is `out v = [decide (|f| + 1 ≤ |t|)]` for `v = ⟨w, ⟨rest, ⟨t, f⟩⟩⟩`. -/
theorem out_eq (v : List Bool) :
    out v = [decide ((true :: pairSndD (pairSndD (pairSndD v))).length ≤
      (pairFstD (pairSndD (pairSndD v))).length)] :=
  rfl

/-- The map `v ↦ fst (snd v)` (the remaining word `rest` of the state word
`⟨w, ⟨rest, ⟨t, f⟩⟩⟩`) is polynomial-time computable. -/
theorem rest_poly : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The map `v ↦ fst (snd (snd v))` (the `true` counter `t` of the state word
`⟨w, ⟨rest, ⟨t, f⟩⟩⟩`) is polynomial-time computable. -/
theorem trues_poly : PolyTimeComputable fun v => pairFstD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The map `v ↦ snd (snd (snd v))` (the `false` counter `f` of the state word
`⟨w, ⟨rest, ⟨t, f⟩⟩⟩`) is polynomial-time computable. -/
theorem falses_poly : PolyTimeComputable fun v => pairSndD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_id.pairEncode (polyTimeComputable_const (pairEncode [] []))

/-- The step is polynomial-time (`Complexity.polyTimeComputable_ite` on the head bit). -/
theorem step_poly : PolyTimeComputable step := by
  have hp : PolyTimeComputable fun v => [(pairFstD (pairSndD v)).headD false] :=
    polyTimeComputable_headD.comp rest_poly
  have h := (((funext fun _ => List.drop_one : (fun w : List Bool => w.drop 1) = List.tail) ▸
      polyTimeComputable_tail).comp rest_poly).pairEncode (polyTimeComputable_ite hp
    (((cons_poly true).comp trues_poly).pairEncode falses_poly)
    (trues_poly.pairEncode ((cons_poly true).comp falses_poly)))
  convert h using 1

/-- The acceptance test is polynomial-time. -/
theorem acc_poly : PolyTimeComputable fun v => [acc v] :=
  polyTimeComputable_isNil.comp rest_poly

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out :=
  lenLe_comp trues_poly ((cons_poly true).comp falses_poly)

/-- After `i ≤ |w|` rounds the state is
`⟨w.drop i, ⟨1^{#true (w.take i)}, 1^{#false (w.take i)}⟩⟩`. -/
theorem orbit_eq (w : List Bool) : ∀ i ≤ w.length, orbit start step w i =
    pairEncode (w.drop i)
      (pairEncode (List.replicate ((w.take i).count true) true)
        (List.replicate ((w.take i).count false) true))
  | 0, _ => by simp [start]
  | i + 1, hi => by
    rw [orbit_succ, orbit_eq w i (Nat.le_of_succ_le hi)]
    obtain ⟨c, hc⟩ : ∃ c, w[i]? = some c := ⟨_, List.getElem?_eq_getElem hi⟩
    have htake : w.take (i + 1) = w.take i ++ [c] := by rw [List.take_succ, hc]; rfl
    have hhead : (w.drop i).headD false = c := by
      rw [List.headD_eq_head?_getD, List.head?_drop, hc]; rfl
    simp only [step, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop, hhead, htake,
      List.count_append]
    cases c <;> simp [List.replicate_succ]

/-- The states of the first `|w|` rounds have length at most `5|w| + 4`. -/
theorem orbit_length_le (w : List Bool) (i : ℕ) (hi : i ≤ w.length) :
    (orbit start step w i).length ≤ 5 * w.length + 4 := by
  rw [orbit_eq w i hi, length_pairEncode, length_pairEncode, List.length_replicate,
    List.length_replicate, List.length_drop]
  have h1 : (w.take i).count true ≤ (w.take i).length := List.count_le_length
  have h2 : (w.take i).count false ≤ (w.take i).length := List.count_le_length
  rw [List.length_take] at h1 h2
  omega

/-- Before round `|w|` the remaining word is nonempty, so `acc` is `false`. -/
theorem acc_orbit_false (w : List Bool) (i : ℕ) (hi : i < w.length) :
    acc (pairEncode w (orbit start step w i)) = false := by
  rw [orbit_eq w i hi.le]
  simp [acc, List.drop_eq_nil_iff, hi]

/-- At round `|w|` the remaining word is empty, so `acc` is `true`. -/
theorem acc_orbit_true (w : List Bool) :
    acc (pairEncode w (orbit start step w w.length)) = true := by
  rw [orbit_eq w w.length le_rfl]
  simp [acc]

/-- At round `|w|` the output is the majority verdict `[decide (|w| < 2 · #true w)]`
(`List.count_true_add_count_false`). -/
theorem out_orbit (w : List Bool) :
    out (pairEncode w (orbit start step w w.length)) = [decide (w.length < 2 * w.count true)] := by
  rw [orbit_eq w w.length le_rfl]
  simp only [out, pairFstD_pairEncode, pairSndD_pairEncode, List.take_length, List.length_cons,
    List.length_replicate]
  have := List.count_true_add_count_false w
  congr 1
  exact decide_eq_decide.mpr ⟨fun h' => by omega, fun h' => by omega⟩

end MajLoop

/-! ### `pairXor`: consume both components, emitting one xor bit per round -/

namespace XorLoop

/-- The initial state `⟨fst z, ⟨snd z, []⟩⟩`: both components remain, empty accumulator. -/
def start (z : List Bool) : List Bool := pairEncode (pairFstD z) (pairEncode (pairSndD z) [])

/-- The initial state is `start z = ⟨fst z, ⟨snd z, []⟩⟩`. -/
theorem start_eq (z : List Bool) : start z = pairEncode (pairFstD z) (pairEncode (pairSndD z) []) :=
  rfl

/-- The step on `⟨z, ⟨a, ⟨b, c⟩⟩⟩`: `⟨a.tail, ⟨b.tail, c ++ [xor (head a) (head b)]⟩⟩`. -/
def step (v : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD v)).tail
    (pairEncode (pairFstD (pairSndD (pairSndD v))).tail
      (pairSndD (pairSndD (pairSndD v)) ++
        [xor ((pairFstD (pairSndD v)).headD false)
          ((pairFstD (pairSndD (pairSndD v))).headD false)]))

/-- The step on `v = ⟨z, ⟨a, ⟨b, c⟩⟩⟩` is `⟨a.tail, ⟨b.tail, c ++ [xor (head a) (head b)]⟩⟩`,
the heads read with default `false`. -/
theorem step_eq (v : List Bool) :
    step v =
      pairEncode (pairFstD (pairSndD v)).tail
        (pairEncode (pairFstD (pairSndD (pairSndD v))).tail
          (pairSndD (pairSndD (pairSndD v)) ++
            [xor ((pairFstD (pairSndD v)).headD false)
              ((pairFstD (pairSndD (pairSndD v))).headD false)])) :=
  rfl

/-- The acceptance test: one of the two remaining components is empty. -/
def acc (v : List Bool) : Bool :=
  decide (pairFstD (pairSndD v) = []) || decide (pairFstD (pairSndD (pairSndD v)) = [])

/-- The acceptance test is `acc v = decide (a = []) || decide (b = [])` for
`v = ⟨z, ⟨a, ⟨b, c⟩⟩⟩`. -/
theorem acc_eq (v : List Bool) :
    acc v =
      (decide (pairFstD (pairSndD v) = []) || decide (pairFstD (pairSndD (pairSndD v)) = [])) :=
  rfl

/-- The output: the accumulator. -/
def out (v : List Bool) : List Bool := pairSndD (pairSndD (pairSndD v))

/-- The output is the accumulator: `out v = c` for `v = ⟨z, ⟨a, ⟨b, c⟩⟩⟩`. -/
theorem out_eq (v : List Bool) : out v = pairSndD (pairSndD (pairSndD v)) :=
  rfl

/-- The number of rounds: the length of the shorter component. -/
def rounds (z : List Bool) : ℕ := min (pairFstD z).length (pairSndD z).length

/-- The number of rounds is `rounds z = min |fst z| |snd z|`. -/
theorem rounds_eq (z : List Bool) : rounds z = min (pairFstD z).length (pairSndD z).length :=
  rfl

/-- The map `v ↦ fst (snd v)` (the remaining first component `a` of the state word
`⟨z, ⟨a, ⟨b, c⟩⟩⟩`) is polynomial-time computable. -/
theorem fstRest_poly : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The map `v ↦ fst (snd (snd v))` (the remaining second component `b` of the state word
`⟨z, ⟨a, ⟨b, c⟩⟩⟩`) is polynomial-time computable. -/
theorem sndRest_poly : PolyTimeComputable fun v => pairFstD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The map `v ↦ snd (snd (snd v))` (the accumulator `c` of the state word
`⟨z, ⟨a, ⟨b, c⟩⟩⟩`) is polynomial-time computable. -/
theorem accum_poly : PolyTimeComputable fun v => pairSndD (pairSndD (pairSndD v)) :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The map `v ↦ [xor (head a) (head b)]` (the xor of the head bits of the two remaining
components of the state word `⟨z, ⟨a, ⟨b, c⟩⟩⟩`, heads read with default `false`, as a one-bit
output) is polynomial-time computable. -/
theorem xorBit_poly : PolyTimeComputable fun v =>
    [xor ((pairFstD (pairSndD v)).headD false)
      ((pairFstD (pairSndD (pairSndD v))).headD false)] := by
  have hpa : PolyTimeComputable fun v => [(pairFstD (pairSndD v)).headD false] :=
    polyTimeComputable_headD.comp fstRest_poly
  have hpb : PolyTimeComputable fun v => [(pairFstD (pairSndD (pairSndD v))).headD false] :=
    polyTimeComputable_headD.comp sndRest_poly
  exact BinArith.polyTimeComputable_xor hpa hpb

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step :=
  (((funext fun _ => List.drop_one : (fun w : List Bool => w.drop 1) = List.tail) ▸
      polyTimeComputable_tail).comp fstRest_poly).pairEncode
    ((((funext fun _ => List.drop_one : (fun w : List Bool => w.drop 1) = List.tail) ▸
      polyTimeComputable_tail).comp sndRest_poly).pairEncode (accum_poly.append xorBit_poly))

/-- The acceptance test is polynomial-time. -/
theorem acc_poly : PolyTimeComputable fun v => [acc v] := by
  have ha : PolyTimeComputable fun v => [decide (pairFstD (pairSndD v) = [])] :=
    polyTimeComputable_isNil.comp fstRest_poly
  have hb : PolyTimeComputable fun v => [decide (pairFstD (pairSndD (pairSndD v)) = [])] :=
    polyTimeComputable_isNil.comp sndRest_poly
  exact polyTimeComputable_or ha hb

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := accum_poly

/-- After `i ≤ rounds z` rounds the state is
`⟨a.drop i, ⟨b.drop i, (zipWith xor a b).take i⟩⟩` with `a = fst z`, `b = snd z`. -/
theorem orbit_eq (z : List Bool) : ∀ i ≤ rounds z, orbit start step z i =
    pairEncode ((pairFstD z).drop i)
      (pairEncode ((pairSndD z).drop i) ((List.zipWith xor (pairFstD z) (pairSndD z)).take i))
  | 0, _ => by simp [start]
  | i + 1, hi => by
    rw [orbit_succ, orbit_eq z i (Nat.le_of_succ_le hi)]
    have ha : i < (pairFstD z).length := by unfold rounds at hi; omega
    have hb : i < (pairSndD z).length := by unfold rounds at hi; omega
    have hza : (pairFstD z)[i]? = some (pairFstD z)[i] := List.getElem?_eq_getElem ha
    have hzb : (pairSndD z)[i]? = some (pairSndD z)[i] := List.getElem?_eq_getElem hb
    have hzip : (List.zipWith xor (pairFstD z) (pairSndD z))[i]? =
        some (xor (pairFstD z)[i] (pairSndD z)[i]) := by
      rw [List.getElem?_zipWith, hza, hzb]
    simp only [step, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop,
      List.headD_eq_head?_getD, List.head?_drop, hza, hzb, Option.getD_some, List.take_succ, hzip,
      Option.toList_some]

/-- The states of the first `rounds z` rounds have length at most `5|z| + 4`. -/
theorem orbit_length_le (z : List Bool) (i : ℕ) (hi : i ≤ rounds z) :
    (orbit start step z i).length ≤ 5 * z.length + 4 := by
  rw [orbit_eq z i hi, length_pairEncode, length_pairEncode, List.length_drop, List.length_drop,
    List.length_take, List.length_zipWith]
  have := length_pair_components_le z
  omega

/-- Before round `rounds z` both remaining components are nonempty, so `acc` is `false`. -/
theorem acc_orbit_false (z : List Bool) (i : ℕ) (hi : i < rounds z) :
    acc (pairEncode z (orbit start step z i)) = false := by
  rw [orbit_eq z i hi.le]
  unfold rounds at hi
  simp only [acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, List.drop_eq_nil_iff]
  omega

/-- At round `rounds z` one remaining component is empty, so `acc` is `true`. -/
theorem acc_orbit_true (z : List Bool) :
    acc (pairEncode z (orbit start step z (rounds z))) = true := by
  rw [orbit_eq z _ le_rfl]
  simp only [acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_true_iff,
    decide_eq_true_eq, List.drop_eq_nil_iff, rounds]
  omega

/-- At round `rounds z` the output is `zipWith xor (fst z) (snd z)`. -/
theorem out_orbit (z : List Bool) :
    out (pairEncode z (orbit start step z (rounds z))) =
      List.zipWith xor (pairFstD z) (pairSndD z) := by
  rw [orbit_eq z _ le_rfl]
  simp only [out, pairSndD_pairEncode]
  have : rounds z = (List.zipWith xor (pairFstD z) (pairSndD z)).length := by
    rw [List.length_zipWith]; rfl
  rw [this, List.take_length]

end XorLoop

/-! ### `pairEq`: consume both components, recording the first mismatch -/

namespace EqLoop

/-- The step on `⟨z, ⟨a, ⟨b, flag⟩⟩⟩`: `⟨a.tail, ⟨b.tail, flag'⟩⟩` where `flag'` is `[true]` if the
head bits differ and `flag` otherwise (`[]` means "no mismatch so far"). -/
def step (v : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD v)).tail
    (pairEncode (pairFstD (pairSndD (pairSndD v))).tail
      (if xor ((pairFstD (pairSndD v)).headD false)
          ((pairFstD (pairSndD (pairSndD v))).headD false) then [true]
        else pairSndD (pairSndD (pairSndD v))))

/-- The step on `v = ⟨z, ⟨a, ⟨b, flag⟩⟩⟩` is `⟨a.tail, ⟨b.tail, flag'⟩⟩` with `flag' = [true]`
if `xor (head a) (head b)` (heads read with default `false`) and `flag' = flag` otherwise. -/
theorem step_eq (v : List Bool) :
    step v =
      pairEncode (pairFstD (pairSndD v)).tail
        (pairEncode (pairFstD (pairSndD (pairSndD v))).tail
          (if xor ((pairFstD (pairSndD v)).headD false)
              ((pairFstD (pairSndD (pairSndD v))).headD false) then [true]
            else pairSndD (pairSndD (pairSndD v)))) :=
  rfl

/-- The output: both remaining components are empty and no mismatch was recorded. -/
def out (v : List Bool) : List Bool :=
  [decide (pairFstD (pairSndD v) = []) && decide (pairFstD (pairSndD (pairSndD v)) = []) &&
    decide (pairSndD (pairSndD (pairSndD v)) = [])]

/-- The output is `out v = [decide (a = []) && decide (b = []) && decide (flag = [])]` for
`v = ⟨z, ⟨a, ⟨b, flag⟩⟩⟩`. -/
theorem out_eq (v : List Bool) :
    out v =
      [decide (pairFstD (pairSndD v) = []) && decide (pairFstD (pairSndD (pairSndD v)) = []) &&
        decide (pairSndD (pairSndD (pairSndD v)) = [])] :=
  rfl

/-- The mismatch flag after `i` rounds: `[]` if the first `i` bits agree, `[true]` otherwise. -/
def flag (a b : List Bool) (i : ℕ) : List Bool := if a.take i = b.take i then [] else [true]

/-- The flag is `flag a b i = []` if `a.take i = b.take i`, and `[true]` otherwise. -/
theorem flag_eq (a b : List Bool) (i : ℕ) :
    flag a b i = if a.take i = b.take i then [] else [true] :=
  rfl

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step :=
  (((funext fun _ => List.drop_one : (fun w : List Bool => w.drop 1) = List.tail) ▸
      polyTimeComputable_tail).comp XorLoop.fstRest_poly).pairEncode
    ((((funext fun _ => List.drop_one : (fun w : List Bool => w.drop 1) = List.tail) ▸
      polyTimeComputable_tail).comp XorLoop.sndRest_poly).pairEncode
      (polyTimeComputable_ite XorLoop.xorBit_poly (polyTimeComputable_const [true])
        XorLoop.accum_poly))

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := by
  have ha : PolyTimeComputable fun v => [decide (pairFstD (pairSndD v) = [])] :=
    polyTimeComputable_isNil.comp XorLoop.fstRest_poly
  have hb : PolyTimeComputable fun v => [decide (pairFstD (pairSndD (pairSndD v)) = [])] :=
    polyTimeComputable_isNil.comp XorLoop.sndRest_poly
  have hc : PolyTimeComputable fun v => [decide (pairSndD (pairSndD (pairSndD v)) = [])] :=
    polyTimeComputable_isNil.comp XorLoop.accum_poly
  exact polyTimeComputable_and (polyTimeComputable_and ha hb) hc

/-- Two words ending in one bit each are equal iff their bodies and their last bits are. -/
theorem append_singleton_eq_iff (l₁ l₂ : List Bool) (c₁ c₂ : Bool) :
    l₁ ++ [c₁] = l₂ ++ [c₂] ↔ l₁ = l₂ ∧ c₁ = c₂ := by
  constructor
  · intro h
    exact ⟨List.append_inj_left' h rfl, List.singleton_inj.mp (List.append_inj_right' h rfl)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The flag after `i + 1` rounds: set if the `i`-th bits differ, else unchanged. -/
theorem flag_succ (a b : List Bool) (i : ℕ) (ca cb : Bool) (hca : a[i]? = some ca)
    (hcb : b[i]? = some cb) :
    flag a b (i + 1) = if xor ca cb then [true] else flag a b i := by
  unfold flag
  rw [List.take_succ, List.take_succ, hca, hcb, Option.toList_some, Option.toList_some]
  cases ca <;> cases cb <;> simp [append_singleton_eq_iff]

/-- The flag has length at most one. -/
theorem length_flag_le (a b : List Bool) (i : ℕ) : (flag a b i).length ≤ 1 := by
  unfold flag
  split_ifs <;> simp

/-- After `i ≤ XorLoop.rounds z` rounds the state is
`⟨a.drop i, ⟨b.drop i, flag a b i⟩⟩` with `a = fst z`, `b = snd z`. -/
theorem orbit_eq (z : List Bool) : ∀ i ≤ XorLoop.rounds z, orbit XorLoop.start step z i =
    pairEncode ((pairFstD z).drop i)
      (pairEncode ((pairSndD z).drop i) (flag (pairFstD z) (pairSndD z) i))
  | 0, _ => by simp [XorLoop.start, flag]
  | i + 1, hi => by
    rw [orbit_succ, orbit_eq z i (Nat.le_of_succ_le hi)]
    have ha : i < (pairFstD z).length := by unfold XorLoop.rounds at hi; omega
    have hb : i < (pairSndD z).length := by unfold XorLoop.rounds at hi; omega
    have hza : (pairFstD z)[i]? = some (pairFstD z)[i] := List.getElem?_eq_getElem ha
    have hzb : (pairSndD z)[i]? = some (pairSndD z)[i] := List.getElem?_eq_getElem hb
    rw [flag_succ _ _ i _ _ hza hzb]
    simp only [step, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop,
      List.headD_eq_head?_getD, List.head?_drop, hza, hzb, Option.getD_some]

/-- The states of the first `rounds z` rounds have length at most `5|z| + 5`. -/
theorem orbit_length_le (z : List Bool) (i : ℕ) (hi : i ≤ XorLoop.rounds z) :
    (orbit XorLoop.start step z i).length ≤ 5 * z.length + 5 := by
  rw [orbit_eq z i hi, length_pairEncode, length_pairEncode, List.length_drop, List.length_drop]
  have := length_pair_components_le z
  have := length_flag_le (pairFstD z) (pairSndD z) i
  omega

/-- Before round `XorLoop.rounds z` both remaining components are nonempty, so `XorLoop.acc`
is `false`. -/
theorem acc_orbit_false (z : List Bool) (i : ℕ) (hi : i < XorLoop.rounds z) :
    XorLoop.acc (pairEncode z (orbit XorLoop.start step z i)) = false := by
  rw [orbit_eq z i hi.le]
  unfold XorLoop.rounds at hi
  simp only [XorLoop.acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, List.drop_eq_nil_iff]
  omega

/-- At round `XorLoop.rounds z` one remaining component is empty, so `XorLoop.acc` is `true`. -/
theorem acc_orbit_true (z : List Bool) :
    XorLoop.acc (pairEncode z (orbit XorLoop.start step z (XorLoop.rounds z))) = true := by
  rw [orbit_eq z _ le_rfl]
  simp only [XorLoop.acc, pairFstD_pairEncode, pairSndD_pairEncode, Bool.or_eq_true_iff,
    decide_eq_true_eq, List.drop_eq_nil_iff, XorLoop.rounds]
  omega

/-- The verdict read off the final state is the equality test. -/
theorem verdict_eq (a b : List Bool) :
    (decide (a.drop (min a.length b.length) = []) && decide (b.drop (min a.length b.length) = []) &&
      decide (flag a b (min a.length b.length) = [])) = decide (a = b) := by
  by_cases hab : a = b
  · subst hab
    simp [flag]
  · rw [decide_eq_false hab]
    rcases Nat.lt_trichotomy a.length b.length with hl | hl | hl
    · rw [Nat.min_eq_left hl.le]
      have : ¬ (b.drop a.length = []) := by rw [List.drop_eq_nil_iff]; omega
      simp [this]
    · rw [Nat.min_eq_left hl.le]
      have : flag a b a.length = [true] := by
        unfold flag
        rw [List.take_length, hl, List.take_length, if_neg hab]
      simp [this]
    · rw [Nat.min_eq_right hl.le]
      have : ¬ (a.drop b.length = []) := by rw [List.drop_eq_nil_iff]; omega
      simp [this]

/-- At round `rounds z` the output is `[decide (fst z = snd z)]`. -/
theorem out_orbit (z : List Bool) :
    out (pairEncode z (orbit XorLoop.start step z (XorLoop.rounds z))) =
      [decide (pairFstD z = pairSndD z)] := by
  rw [orbit_eq z _ le_rfl]
  simp only [out, pairFstD_pairEncode, pairSndD_pairEncode, XorLoop.rounds]
  rw [verdict_eq]

end EqLoop

/-! ### `blockMap`: consume the second component block by block -/

namespace BlockMapLoop

/-- The initial state `⟨snd z, []⟩`: the whole second component remains, empty accumulator. -/
def start (z : List Bool) : List Bool := pairEncode (pairSndD z) []

/-- The initial state is `start z = ⟨snd z, []⟩`. -/
theorem start_eq (z : List Bool) : start z = pairEncode (pairSndD z) [] :=
  rfl

/-- The block length read off the state word `⟨z, s⟩`: `b(|fst z|)`. -/
private def blk (b : PolyExpr) (v : List Bool) : ℕ := b.eval (pairFstD (pairFstD v)).length

/-- The step on `⟨z, ⟨rest, c⟩⟩`: `⟨rest.drop k, c ++ g (rest.take k)⟩` with `k = b(|fst z|)`. -/
def step (b : PolyExpr) (g : List Bool → List Bool) (v : List Bool) : List Bool :=
  pairEncode ((pairFstD (pairSndD v)).drop (blk b v))
    (pairSndD (pairSndD v) ++ g ((pairFstD (pairSndD v)).take (blk b v)))

/-- The step on `v = ⟨z, ⟨rest, c⟩⟩` is `⟨rest.drop k, c ++ g (rest.take k)⟩` with the block
length `k = b(|fst z|)`. -/
theorem step_eq (b : PolyExpr) (g : List Bool → List Bool) (v : List Bool) :
    step b g v =
      pairEncode ((pairFstD (pairSndD v)).drop (b.eval (pairFstD (pairFstD v)).length))
        (pairSndD (pairSndD v) ++
          g ((pairFstD (pairSndD v)).take (b.eval (pairFstD (pairFstD v)).length))) :=
  rfl

/-- The acceptance test: fewer than `k` bits remain, or `k = 0`. -/
def acc (b : PolyExpr) (v : List Bool) : Bool :=
  decide ((true :: pairFstD (pairSndD v)).length ≤ blk b v) || decide (blk b v ≤ 0)

/-- The acceptance test on `v = ⟨z, ⟨rest, c⟩⟩` is `decide (|rest| + 1 ≤ k) || decide (k ≤ 0)`
with the block length `k = b(|fst z|)`. -/
theorem acc_eq (b : PolyExpr) (v : List Bool) :
    acc b v =
      (decide ((true :: pairFstD (pairSndD v)).length ≤ b.eval (pairFstD (pairFstD v)).length) ||
        decide (b.eval (pairFstD (pairFstD v)).length ≤ 0)) :=
  rfl

/-- The output: the accumulator. -/
def out (v : List Bool) : List Bool := pairSndD (pairSndD v)

/-- The output is the accumulator: `out v = c` for `v = ⟨z, ⟨rest, c⟩⟩`. -/
theorem out_eq (v : List Bool) : out v = pairSndD (pairSndD v) :=
  rfl

/-- The number of rounds: the number of full blocks `|snd z| / b(|fst z|)`. -/
def rounds (b : PolyExpr) (z : List Bool) : ℕ :=
  (pairSndD z).length / b.eval (pairFstD z).length

/-- The number of rounds is `rounds b z = |snd z| / b(|fst z|)` (natural division, `0` when
`b(|fst z|) = 0`). -/
theorem rounds_eq (b : PolyExpr) (z : List Bool) :
    rounds b z = (pairSndD z).length / b.eval (pairFstD z).length :=
  rfl

/-- The map `v ↦ fst (fst v)` (the parameter `fst z` of the state word `⟨z, ⟨rest, c⟩⟩`) is
polynomial-time computable. Any first component works: only its length is used, as the
argument of the block length `b`. -/
theorem param_poly : PolyTimeComputable fun v => pairFstD (pairFstD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- The map `v ↦ fst (snd v)` (the remaining word `rest` of the state word `⟨z, ⟨rest, c⟩⟩`) is
polynomial-time computable. -/
theorem rest_poly : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The map `v ↦ snd (snd v)` (the accumulator `c` of the state word `⟨z, ⟨rest, c⟩⟩`) is
polynomial-time computable. -/
theorem accum_poly : PolyTimeComputable fun v => pairSndD (pairSndD v) :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [])

/-- The step is polynomial-time (the typed cuts `Complexity.polyTimeComputable_pairDropPoly`
and `polyTimeComputable_pairTakePoly` on `⟨fst (fst v), rest⟩`). -/
theorem step_poly (b : PolyExpr) {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (step b g) := by
  have hdrop : PolyTimeComputable fun v => (pairFstD (pairSndD v)).drop (blk b v) := by
    convert (polyTimeComputable_pairDropPoly b).comp (param_poly.pairEncode rest_poly) using 1
    funext v
    simp [blk]
  have htake : PolyTimeComputable fun v => (pairFstD (pairSndD v)).take (blk b v) := by
    convert (polyTimeComputable_pairTakePoly b).comp (param_poly.pairEncode rest_poly) using 1
    funext v
    simp [blk]
  exact hdrop.pairEncode (accum_poly.append (hg.comp htake))

/-- The acceptance test is polynomial-time (two length tests against `1^{k}`). -/
theorem acc_poly (b : PolyExpr) : PolyTimeComputable fun v => [acc b v] := by
  have h1 : PolyTimeComputable fun v =>
      [decide ((true :: pairFstD (pairSndD v)).length ≤ blk b v)] := by
    convert lenLe_comp (unaryPoly_comp b param_poly) ((cons_poly true).comp rest_poly) using 1
    funext v
    simp [blk]
  have h2 : PolyTimeComputable fun v => [decide (blk b v ≤ 0)] := by
    convert lenLe_comp (polyTimeComputable_const []) (unaryPoly_comp b param_poly) using 1
    funext v
    simp [blk]
  exact polyTimeComputable_or h1 h2

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out := accum_poly

/-- After `i` rounds (any `i`) the state is, with `k = b(|fst z|)` and `s = snd z`,
`⟨s.drop (i k), g (block 0) ++ ⋯ ++ g (block (i-1))⟩` where `block j = (s.drop (j k)).take k`. -/
theorem orbit_eq (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) (i : ℕ) :
    orbit start (step b g) z i =
      pairEncode ((pairSndD z).drop (i * b.eval (pairFstD z).length))
        ((List.range i).flatMap fun j =>
          g (((pairSndD z).drop (j * b.eval (pairFstD z).length)).take
            (b.eval (pairFstD z).length))) := by
  induction i with
  | zero => simp [start]
  | succ i ih =>
    rw [orbit_succ, ih, Nat.succ_mul]
    simp only [step, blk, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop,
      List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The states of the first `rounds b z` rounds have length at most
`2|z| + 2 + |z| · C (b(|z|) + 1)^c` when `|g y| ≤ C (|y| + 1)^c`.

**Proof sketch.** By `orbit_eq` the state is `⟨(snd z).drop (i k), acc_i⟩` with `k = b(|fst z|)`
and `acc_i` the concatenation of `i` chunks `g (block j)`; each block has length at most
`k ≤ b(|z|)` (`PolyExpr.eval_mono`, `Complexity.length_pairFstD_le`), so each chunk has length
at most `C (b(|z|) + 1)^c`, and `StateLoop.length_flatMap_range_le` bounds `|acc_i|` by
`i · C (b(|z|) + 1)^c ≤ |z| · C (b(|z|) + 1)^c` since `i ≤ |snd z| / k ≤ |z|`
(`Nat.div_le_self`, `length_pair_components_le`); `PolyExpr.eval_subst` and
`PolyExpr.eval_normal` identify the bound with the stated expression. -/
theorem orbit_length_le (b : PolyExpr) (g : List Bool → List Bool) (C c : ℕ)
    (hg : ∀ y, (g y).length ≤ C * (y.length + 1) ^ c) (z : List Bool) (i : ℕ)
    (hi : i ≤ rounds b z) :
    (orbit start (step b g) z i).length ≤
      (PolyExpr.add (.mul (.const 2) .var)
        (.add (.const 2) (.mul .var ((PolyExpr.normal C c).subst b)))).eval z.length := by
  rw [orbit_eq, length_pairEncode, List.length_drop]
  have hk : b.eval (pairFstD z).length ≤ b.eval z.length := b.eval_mono (length_pairFstD_le z)
  have hzs := length_pair_components_le z
  have hi' : i ≤ z.length :=
    hi.trans ((Nat.div_le_self _ _).trans (by omega))
  have hchunk : ∀ j < i, (g (((pairSndD z).drop (j * b.eval (pairFstD z).length)).take
      (b.eval (pairFstD z).length))).length ≤ C * (b.eval z.length + 1) ^ c := by
    intro j _
    refine (hg _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    rw [List.length_take]
    omega
  have hfm := length_flatMap_range_le _ _ i hchunk
  have hle := hfm.trans (Nat.mul_le_mul_right _ hi')
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
    PolyExpr.eval_subst, PolyExpr.eval_normal]
  generalize z.length * (C * (b.eval z.length + 1) ^ c) = Q at hle
  omega

/-- Before round `rounds b z` at least `k` bits remain and `k > 0`, so `acc` is `false`. -/
theorem acc_orbit_false (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) (i : ℕ)
    (hi : i < rounds b z) : acc b (pairEncode z (orbit start (step b g) z i)) = false := by
  rw [orbit_eq]
  simp only [acc, blk, pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons,
    List.length_drop, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  unfold rounds at hi
  have hk : 0 < b.eval (pairFstD z).length := by
    rcases Nat.eq_zero_or_pos (b.eval (pairFstD z).length) with h0 | h0
    · rw [h0, Nat.div_zero] at hi
      omega
    · exact h0
  have hmul := (Nat.le_div_iff_mul_le hk).mp hi
  rw [Nat.succ_mul] at hmul
  omega

/-- At round `rounds b z` fewer than `k` bits remain (or `k = 0`), so `acc` is `true`. -/
theorem acc_orbit_true (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) :
    acc b (pairEncode z (orbit start (step b g) z (rounds b z))) = true := by
  rw [orbit_eq]
  simp only [acc, blk, pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons,
    List.length_drop, Bool.or_eq_true_iff, decide_eq_true_eq, rounds]
  rcases Nat.eq_zero_or_pos (b.eval (pairFstD z).length) with hk | hk
  · right
    omega
  · left
    have h1 := Nat.lt_mul_div_succ (pairSndD z).length hk
    have h2 := Nat.div_mul_le_self (pairSndD z).length (b.eval (pairFstD z).length)
    rw [Nat.mul_succ, Nat.mul_comm (b.eval (pairFstD z).length)] at h1
    omega

/-- At round `rounds b z` the output is the concatenation of `g` over the full blocks. -/
theorem out_orbit (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) :
    out (pairEncode z (orbit start (step b g) z (rounds b z))) =
      (List.range (rounds b z)).flatMap fun i =>
        g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take
          (b.eval (pairFstD z).length)) := by
  rw [orbit_eq]
  simp [out]

end BlockMapLoop

end Complexity.StateLoop
```

## ===== policy.md (records, at 2da7e0f3cd65ec93ed71813b7828c3b66ba18942) =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/pass-shelat-ch5-8/gates/42-sc-yao/pack.md (records, at 2da7e0f3cd65ec93ed71813b7828c3b66ba18942) =====

# Gate 42 · Yao's protocol in the OT-hybrid model (`sc-yao`, U3, [PS10, Protocol 162.6, Theorem 163.7])

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #341](https://github.com/Shilun-Allan-Li/tcslib/pull/341) at
  `e9b03c437aca251846430ff23b40ee5ff3d3347a` (branch `land/pass-shelat-sc-yao`, tree
  `3a770d2979fc847e3948dc79ca42ba7db3f0b906`).
- **Records pin:** `f22e0f6798815b9263893e61928b4f16452f74ee` ("sc-yao review r1 final"). Every record this pack cites is
  read at the pin (the interim review at its own commit, and the rulings below at theirs). The pack's own files are filed
  by the maintainer after this pin.
- **Rulings after the pin:** records commit `67423db6c9d6448ae531b04f42c315585d00d502` (a descendant of the pin; records
  only, no Lean, lake, `audits` or `scripts` path changed) adds Seyoon's rulings of 2026-11-16 on SY-F01 to SY-F03
  (`fills/sc-yao/final-r1/rulings.md`), ledger row **DL-51** and the **DL-49 extension** in
  `briefs/pass-shelat-ch5-8/duplication-ledger.md` (and DW-4's scope in `deferred-work.md`). None of them changes #341.
  SY-F01 is confirmed; SY-F02 goes on the ledger, then is promoted (DL-51); SY-F03 puts both copies on the ledger, with
  promotion later (DL-49). Still open: SY-F05's remaining pair (ruling 10 below).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4`; its merge base is the old tip
  `f9fda8fe8d11fc68c233df2979a86d356ddfe1ab` (with #313, #318, #319, #323, #326, #332 and #333).
  - The fill was issued on `6ce4658db08a1dc2a03a149987197660db078011`, before sc-garble (#323) merged, under the
    proved-modulo rule: `yaoHybrid_simulators` cites sc-garble's frozen `yaoSeed_good_whp` and
    `sliceMultiMessageSecure_of_prfOut`. Both are proved on `f9fda8fe`, so on the landing head the targets use only the
    standard axioms.
  - Since `f9fda8fe` the branch gained #327 (seq-zk, `7d532e20`) and #324 (sc-compose,
    `201bf57a941131d1737295089ffd7477e1d7f7b9`) and records. Neither touches the PR's 70 paths, and between `201bf57a`
    and the pin no Lean, lake, `audits` or `scripts` path changes (`pack-checks/series.txt`).
  - `pr.diff.txt` is `git diff f9fda8fe..e9b03c43`, which equals the three-dot `git diff f22e0f67...e9b03c43` (GitHub's
    view) byte for byte: 70 paths, 15813 insertions, 67 deletions.
  - **Not an audit item.** The integration build of the head on the current tip (with #327 and #324, `201bf57a`) is a
    maintainer merge condition and is running separately. `git merge-tree` of the head with `201bf57a` and with the pin
    is clean, no path is shared, and no module of the PR's import closure changed between `f9fda8fe` and `201bf57a`
    (`pack-checks/mergetrees.txt`).
- **Commits:** 12, all committed by Claude and SSH-signed with the key that signs the records pin; each signature
  verifies, and a one-byte tamper control fails (`pack-checks/series.txt`).
  - The worker's 8 commits (job `sc-yao`: a lead and 3 sub-agents on Seyoon's Mac under the host addendum, ruling SY-6;
    author Seyoon Ragavan), delivered unsigned with a `COMMITS.tsv` signing column `none`. `git am` at the issue base
    reproduces all 8 hashes (`6ce4658d..6e7ef601`). They were cherry-picked onto `f9fda8fe`, author kept:
    `git range-diff` is 5/8 `=`; commit 1 lost the `DAGCircuit.isFaninTwo_iff` hunk, which the merge absorbed because it
    is byte-identical to #323's, and commits 4 and 7 differ only in the `## Main results` bullet resolution.
  - Landing edits: **LE-bullet** `13690d2e`, **LE-reuse** `81d526d8` (SY-F05), **LE-title** `bd7832d7` (optional) and
    **LE-doc** `e9b03c43` (the head; SY-F04, a separate job, fast-forwarded).
- **Scope:** a **proof audit** of two admitted, frozen statements of `SecureComputation/Yao.lean`, and of what consumes
  them:

  | Target | Line at the head | Source |
  |---|---|---|
  | `yaoHybrid_polyTime` | 863 | [PS10, Definition 155.1] (the efficiency clause, ruling of 2026-11-05), for Protocol 162.6 in the OT-hybrid model |
  | `yaoHybrid_simulators` | 1021 | [PS10, Theorem 163.7] in the OT-hybrid model; the one-active-key simulator of [LP09] |
  | `yaoHybrid_hbcSecure` (proved at the base from the two, unchanged) | 1168 | Theorem 163.7 in the OT-hybrid model |

  Both targets passed the prong statement phase and Gate 06 and are frozen; the brief quotes them. `yaoHybrid_hbcSecure`
  consumes both, and `YaoReal.lean`'s `yaoProtocol_hbcSecure` consumes it.
- **Brief:** `fills/sc-yao/issued-r1/brief.md` (SHA-256 `4785f593…`) with **rulings SY-1 to SY-6** (`ruling-SY.md`, which
  overrides the brief where they differ): one hub import line (SY-1), the `Yao.lean` cap waived to 1,200 lines (SY-2),
  the pre-approved SY-3 readers, the SY-4 hosts as public generic contracts, disclosed general copies of unmerged
  deliveries allowed (SY-5), and the multi-agent worker (SY-6). Five checkpoints; the stricter `Yao.lean` rule; the
  visibility rule (helpers state everything generically; the bodies instantiate them); Gate 27's hand-off obligations;
  the binding duplication rule with an `## Overlap and reuse` section; Rule 10 with the projection-coercion ruling and
  seals with `PolyExpr.eval` both excluded and sealed; the docstring and sketch rules; the G26-N1 error count; the
  evidence-completeness rule.

## What changed

Paths are under `TCSlib/Cryptography/SecureComputation/` unless they start with `TCSlib/`. The PR touches 70 files: 2
modified and 68 new (15813 insertions, 67 deletions). Lines are tip → head (`source-head.json`; every line at most 100
characters).

| File | Status | Lines |
|---|---|---:|
| `Yao.lean` | owned regions only (the stricter rule), shared with sc-garble | 970 → 1179 (942 at the issue base; SY-2 cap 1,200) |
| `TCSlib/Complexity/CircuitComplexity/Uniform.lean` | frozen, the seven SY-3 readers | 281 → 307 |
| `Yao/HybridProof.lean` | the hub (new; imports exactly its 67 children; `## Contents`) | 158 |
| `Yao/HybridProof/*.lean` | 67 helpers, new | 15353 together; largest `RowFromCoins` 649 |
| `TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean` | frozen, **unchanged against the tip** | 730 |

`Yao/HybridProof.lean` is the only file directly under `Yao/`; `Yao.lean` imports only the hub, and the facade needs no
edit (#305).

**The proof** (REPORT § *Generic interface and concrete proof assembly*, § *Gate 27 hand-off*; the targets' sketches
were rewritten to describe the delivered proof, the statement prose is unchanged):
1. **`yaoHybrid_polyTime`** (128-line body). `HybridProtocol.PolyTime` (`polyTime_iff`) asks for efficient `main`
   strategies, polynomial-time call inputs and a message bound for any answers.
   - *Alice:* `AliceProgram.message_poly` computes the encoded `garbledTable (nestedSpecial E₁ E₂ n)` vector, her
     selected input keys and the decoding pairs, from `⟨1^n, ⟨x, r⟩⟩`, through the circuit-description decoder (host
     H-SY-decoder, `DescriptionDecoder.decodeDescription_host`, and `ChunkScanner`), `Y.uniform` with
     `encodeCircuit_eq` and `encodeMsgs_eq_encWords`, the seed readers (`keyAt_yaoSeed`, `yaoSeed_snd_fst`,
     `yaoSeed_snd_snd`, `readBits_apply`), fan-in two by `DAGCircuit.isFaninTwo_iff`, and `polyTimeComputable_spEncFun`;
     the noncomputable `Finset.univ.toList` row order is handled for an arbitrary constant enumeration.
   - *Bob:* `BobProgram.output_poly` runs `runWith`/`evalGate` of `nestedSpecial` on tables decoded from an arbitrary
     message (host H-SY-eval, `RunWithHost.exists_machine`, via `GarbledRun.garbledRunWith_poly`), then the output
     decoding.
   - Every history, malformed ones included, goes through the GI efficiency layer (`GI.efficient_of_polyTime`);
     `CallEquations.inputA_eq`/`inputB_eq` give the call inputs through `finProdFinEquiv`; the ciphertext truncation
     bounds give a message bound independent of the answers (`twoMove_message_length_le`).
2. **`yaoHybrid_simulators`** (124-line body). `S_A = AliceSimulator.simulator (yaoCoins Y)` (the copying simulator) and
   `S_B` from `FakeSimulatorFactory.exists_simulator` (the fake garbling with active keys, the real enumeration and
   shifts, the prescribed output), both uniform and chosen before `D`; one negligible `ε` after `D`, before `n`, `x`, `y`.
   - *Statistical part:* the bad event is the frozen `yaoSeed_good_whp` (with `hGE₁`, `hGE₂`, `hG₁`, `hG₂`); off it,
     `yaoHybrid_correct` gives both outputs; `AliceStatistical.distAdv_real_ideal_le` and
     `BobStatistical.statClose_real_output_switch`, with the switch lemmas of `StatisticalSwitch` (SY-F02), which
     `AliceSimulator` and `SimulationBound` use.
   - *Bob's computational part:* `BobStageZero.acceptProb_eq_stage0` (the real view is stage zero up to an exact
     permutation of the coin tape: the point-and-permute relabelling, `CoinRelabel`, `CoinSeedRelabel`,
     `RelabelGarbling`); a gate hybrid with two substeps per gate (`GateHybrids`, `GateHybridMessage`), each reduced to
     the frozen B1 statement `sliceMultiMessageSecure_of_prfOut hG₁₂` with slices `(0, n)` and `(2n, 4n + 2)`
     (`SelectedSlices`) and `7n + 2 ≤ L.eval n` for `L = .add (.add .var .var) (.add .var innerLen)`; a non-uniform
     reduction whose advice is the worst input, the stage and the whole baseline tape (`SelectedStepSecurity`,
     `SliceReduction.reconstruction_negligible`, `SelectedAdviceBounds`); polynomial-time reconstruction
     (`SliceReconstruction`); the chain over at most `2 S(n)` stages (`GateHybridChain`, `GateHybridSecurity`); and the
     last stage equal to `S_B`'s ideal view (`SamplerEndpoints.acceptProb_end_eq_ideal`).
   - *Total:* `simulators_of_output_switch` gives `δ(n) + 2 S(n) · |μ_B1(n)|` for both sides.
3. **`yaoHybrid_hbcSecure`** is unchanged; it now uses only the standard axioms (review § *Axioms*).

**Gate 27's hand-off obligations** (brief § *Proof route*; REPORT § *Gate 27 hand-off*, a declaration map): (1) the gate
and row sub-hybrids; (2) the enumeration of all occurrences of the selected key, with padding (`GateOccurrences`);
(3) the no-dependence argument (`GateOccurrences.selected_wire_lt`, `SelectedFields.stageBit_plaintext_ne_*`,
`SelectedStep.plaintext_ne`, `outs_sink`); (4) the exact coin and view sampler identities (`SelectedTables.*_reconstruct`);
(5) polynomial-time reconstruction (`SliceReconstruction.row_poly`, `tables_poly`, `rebuild_poly`).

**The SY-3 readers** (`Uniform.lean`, pure insertions, each `theorem … := rfl` with a formula docstring and no
attribute, directly after its `def`): `encodeList_nil`, `encodeList_cons`, `GateKind.encode_and`, `encode_or`,
`encode_not`, `DAGGate.encode_eq`, `DAGCircuit.encode_parts`. The worker also delivered `DAGCircuit.isFaninTwo_iff`
byte-identical to sc-garble's approved reader (SG-F01); at landing it coincided with the tip's copy, so `DAGCircuit.lean`
is unchanged.

## Rulings and records in force

1. **SY-1 to SY-6 (Seyoon, 2026-11-15, before dispatch)**, `ruling-SY.md`. In particular SY-2 (`Yao.lean` at most 1,200
   lines, recorded as a size exception) and SY-5 (disclosed general re-derivations of lemmas that existed only in the
   unmerged sc-garble, #318 and sc-compose deliveries are allowed and re-pointed proof-only after landing; copying a
   merged public lemma is still a finding).
2. **SG-F01 (Seyoon confirmed, 2026-11-15):** `DAGCircuit.isFaninTwo_iff`, `Iff.rfl`. It is on the tip from #323; the PR
   does not change `DAGCircuit.lean`.
3. **SY-F01, confirmed (Seyoon, 2026-11-16; `rulings.md` at `67423db6`):** the four helper imports outside the issued
   order, approved in the worker's session (`worker/final/evidence/scope-request/`, quoted in REPORT § *Scope
   requests*): `ZeroKnowledge/ThreeColoring/Machines`, `PrivateKey/FromPRF/ReductionMachine`,
   `PrivateKey/FromPRF/HybridLemmas` (a brief defect: its lemma was a listed interface) and `Asymptotic/BlockEncryptor`.
4. **SY-F02 and SY-F03, ruled (Seyoon, 2026-11-16; `rulings.md` at `67423db6`):**
   - SY-F02: ledger, then promote. **DL-51:** `StatisticalSwitch.statClose_of_eq_off` and `distAdv_le_of_eq_off`
     against `statClose_of_uprob_ne` (`Candidates/DDH.lean:145`); in the cleanup `statClose_of_uprob_ne` moves to
     `Asymptotic/Sampling` and both users are re-pointed.
   - SY-F03: ledger both, promote later. **DL-49 extended** with sc-yao's `YaoHybridProof.encodeMsgs_eq_encWords`
     (`Yao/HybridProof/Lengths.lean:83`) and #327's `SequentialZK.encodeMsgs_eq_encWords`
     (`Composability/SequentialZK/Normalization.lean:40`), as the post-merge addendum proposed; one copy goes to a
     common home in the cleanup.
5. **The duplication ledger** at `67423db6`: DL-46 (the `encodeList_eq_flatMap` copies), DL-47 (the getD/headD-of-
   `List.ofFn` class, which the brief let helpers use inline through Mathlib's `List.getD_eq_getElem`/`List.getElem_ofFn`
   but not copy as a lemma), DL-49 (sc-compose's restatements, among them the `encodeMsgs` relatives, extended by SY-F03)
   and DL-51 (SY-F02). **Not a finding:** any item these rows list, provided the row matches the code.
6. **Rule 10:** `PolyExpr.eval` is notation (Q1, the user, 2026-11-07): seal **A** is canonical, seal B is run and its
   new failures attributed from the raw logs (Gate 31). A `CoeFun`/`Coe` instance whose body is a structure projection
   is notation (Seyoon, 2026-11-14); `FinDist.instCoeFunForallReal` is the only one in the environment, so **coe-A is
   the canonical variant** and the strict variant is run and attributed. Reducible abbreviations are notation
   (2026-10-26). Inside `Yao.lean` its own definitions may be read directly (`rfl`, `show`); each helper is foreign to
   the others.
7. **The facade-completeness lint fix, #305.** The baselines are 92 FAIL / 101 WARN (Cryptography) and 25 / 390
   (Complexity) at the tip.
8. **The host addendum** (`fills/codex-host-2026-11-15/host-addendum.md`, §4 for sub-agents): the review checked the
   3-slot cap from `slots.log`. The worker's shared-wrapper execution authorization
   (`scope-request/execution-authorization.md`) is information, not a finding.
9. **DW-1** (`deferred-work.md`): `HBCSecure` allows non-uniform simulators as [PS10, Definition 155.1] does; making the
   Yao simulators literally `Uniform` is deferred. SY-F11 notes that `S_A` and `S_B` are uniform already. DW-4 (the
   duplication cleanup) now spans DL-38 to DL-51 (`67423db6`).
10. **Still open: SY-F05's remaining pair.** `OTAnswerWords.length_answersB` and `answersA_nil` against #324's now
   public `HybridProtocol.length_answersB` and `length_answersA` (`ComposeSecurity/Lengths.lean:60`, `:52`). The proposed
   disposition is a ledger row, with a re-point after #341 merges; it awaits Seyoon's acknowledgement (`rulings.md`).
   **Grade that disposition.**

## What is frozen

- **The targets' statements** (headers, `include hGE₁ hGE₂ in`, and the statement prose before each `**Proof sketch.**`,
  including the simulators' *Deviation: the joint PRF hypothesis* paragraph) and **every other declaration of
  `Yao.lean`**, private ones included, with every definition body, docstring, `variable`, `section`, `open`,
  `set_option`, import and comment; sc-garble's `yaoSeed_good_whp` (proved on the tip) in full.
- **`Yao.lean` may change in exactly six regions:** the hub import after line 9, the `## Main results` bullet, the two
  sketches and the two bodies; plus **LE-title**'s title line (the brief left "(statement phase)" for the maintainer's
  landing edit). No declaration may be added to `Yao.lean`.
- **`Uniform.lean`** apart from the seven SY-3 readers; **`DAGCircuit.lean`** entirely; every other file
  (`Garbling*`, `SpecialEncryption*`, `Hybrid`, `Defs`, `YaoReal`, `ObliviousTransfer*`, `Compose*`, `Pseudorandom/*`,
  `Encryption/*`, `Games/*`, `ZeroKnowledge/*`, the circuit and complexity libraries).
- **The landing edits:** LE-bullet (one bullet), LE-reuse (proofs only), LE-title (one line), LE-doc (comments only).

## Questions for the audit

**1. Correctness against the frozen statements and [PS10, Protocol 162.6, Theorem 163.7]**
- **`yaoHybrid_polyTime`:** does the body establish all four clauses of `polyTime_iff` for `yaoHybrid Y E₁ E₂`, for
  **every** history (malformed messages, private inputs and tapes; `x.length` against `n`)? Are the two hosts
  (H-SY-decoder, H-SY-eval) correct on every canonical description and polynomial on every string, and is the constant
  enumeration of `Finset.univ.toList` handled soundly? Is the message bound independent of the answers? Do the call-input
  machines read the right coin blocks and choice bits through `finProdFinEquiv`?
- **`yaoHybrid_simulators`:** are `S_A` and `S_B` fixed before `D`, and `ε` before `n`, `x`, `y`? Is Alice's side exactly
  the statistical switch off `yaoSeed_good_whp`'s bad event, and Bob's output switch exactly `yaoHybrid_correct` off it?
  Is the stage-zero identity an exact bijection of Alice's coins (keys `k_w^b ↦ k_w^{b ⊕ v_w}`, rows `a ↦ a ⊕ v_args`,
  shifts `λ_i ↦ λ_i ⊕ v_args`), and is the last stage exactly `S_B`'s ideal view?
- **The B1 embedding:** is every row under the inactive key `ι_u`, in every gate that reads `u`, a challenge slot with
  the right shape (`(0, n)` for a second or only argument, `(2n, 4n + 2)` for a first argument), padded to `q(n) + 1`
  slots with equal messages where nothing changes? Is the interface non-adaptive (every challenge message fixed before
  any challenge ciphertext)? Is the advice (worst input, stage, baseline tape) polynomial (`SelectedAdviceBounds`), the
  reconstruction polynomial-time on every string, and the sampler identity exact? Are **Gate 27's obligations (1)–(5)**
  met by the declarations the REPORT maps them to?
- **The total:** is `δ(n) + 2 S(n) · |μ_B1(n)|` the right bound, negligible by the published polynomial-times-negligible
  theorem, with one `μ` for all neighbouring stages?
- **Against the source:** PS10's proof of Theorem 163.7 (book pages 163–164, `sources.zip` `PS10/`) simulates Bob with a
  garbled circuit that always outputs `f(x, y)` and asserts a hybrid argument; the formal proof runs in the OT-hybrid
  model (Q-5, 2026-11-05; OT composition is sc-compose's `hbcSecure_compose`) with the one-active-key simulator of
  [LP09]. Is that a faithful formalization of Protocol 162.6 and Theorem 163.7 in that model, and are the deviations
  stated?
- **Edge cases** (brief § *Edge cases*): `n = 0`; `inA`, `inB` or `outLen` zero; `|gates| = 0`; constant, one- and
  two-argument gates; output vertices that are inputs or coincide; a wire read in both argument positions (both slice
  shapes under one key); wires read by no gate and unread coin blocks; accidental equal key values.

**2. Frozen-statement integrity**
- **`Yao.lean`:** do only the six approved regions and LE-title's title line change? The pack re-check
  (`pack-checks/frozen.txt`) masks those seven spans at the tip and the head and finds the rest byte-identical (0
  violations, 0 rule breaks), every unmasked hunk inside one region on both sides, the 76 declarations in the same order
  with byte-identical headers and definitions, the two targets' statement prose byte-identical, `yaoSeed_good_whp`
  unchanged, and one added import. Its six controls (a one-character header, an extra frozen line, a second import, a
  declaration smuggled into a body, an edit inside a sketch, a doubled space in statement prose) each give the expected
  count. The review's own check (`frozen_sy.py`, `landing/frozen-check.txt` = `landing/yao-scope-vs-tip-final.txt`)
  masks only the six regions, so it reports exactly **one** violation, the LE-title line; its scope check at the issue
  base, with six controls, is `scope/yao-check.txt` and `scope/controls-results.txt`.
- **`Uniform.lean`:** is the change exactly the seven SY-3 `rfl` readers, pure insertions, each with a formula docstring,
  no attribute, directly after its `def`, and does removing them restore the tip byte for byte (`frozen.txt`,
  `landing/uniform-check.txt`)? Is each reader needed under the seal (`rule10/reader-control-recount.txt`: 8 unsealed
  `rfl` pass, 8 sealed `rfl` fail once, 8 sealed readers pass, `isFaninTwo_iff` included)?
- **`DAGCircuit.lean`:** is it unchanged against the tip, and is the delivered `isFaninTwo_iff` block byte-identical to
  the tip's (`frozen.txt`: the delivery's copy = the issue base plus exactly that block)?
- Is every other changed path a new file under the hub, and is nothing else in a frozen file changed?

**3. The landing edits** (`pack-checks/lecheck.txt`; review evidence `landing/`, `phase2/ledoc/docstrip.txt`)
- **LE-bullet `13690d2e`:** one bullet, "(proved modulo sc-garble)" → "(proved)".
- **LE-reuse `81d526d8` (SY-F05):** `CoinSeedRelabel.assignmentFold_lt_four` and `assignmentFold_injective` now read the
  public `GarblingProbability.assignmentFold_small` (`.1 a`, `.2`); headers byte-identical, no import change, two
  docstrings rewritten. Is it proof-only?
- **LE-title `bd7832d7` (optional):** the title line only.
- **LE-doc `e9b03c43` (SY-F04):** 64 helper files; each is identical after stripping comments (the re-check strips line,
  block and doc comments; 64/64; two controls); `Yao.lean`, `Uniform.lean` and `DAGCircuit.lean` untouched; widths at
  most 100. Do the new formula docstrings state the declarations' formulas correctly, in Lean argument order? (The LE-doc
  job checked one assumption, the argument order of `FakeSimulator.Data.make`, against `#check`;
  `phase2/axioms-summary.txt` shows it.)

**4. Duplication (recent gates graded undisclosed re-proofs of public lemmas as majors)**
- Does any new declaration, or any part of a proof, duplicate a public TCSlib or Mathlib lemma, or copy a private one,
  beyond the REPORT's `## Overlap and reuse` (line 266), the ledger rows of ruling 5 and SY-5's disclosed copies? **An
  undisclosed duplicate of a public lemma is a major.** The recent majors of this class: G23-01, G24-01, prf-mac F-01,
  learning (`uprob_eq_point`), G29-01, G29-02, sc-ot F-01, G34-01.
- **Grade SY-F01 to SY-F12** (the review's table), given the rulings (rulings 3, 4 and 10):
  - **SY-F01** (confirmed): the four helper imports; is each needed, and is the closure growth
    (`layout/external-imports.txt`) acceptable?
  - **SY-F02** (ruled: DL-51, then promote): `StatisticalSwitch.statClose_of_eq_off` and `distAdv_le_of_eq_off` against
    the public `statClose_of_uprob_ne` (`Candidates/DDH.lean:145`), undisclosed (the REPORT never names it);
    `pack-checks/dupscan.txt` shows both texts, and `context/` holds `DDH.lean`.
  - **SY-F03** (ruled: DL-49 extended, promote later): `YaoHybridProof.encodeMsgs_eq_encWords` (`Lengths.lean:83`)
    against `ColMachines.encodeMsgs_eq_flatMap` (`ThreeColoring/Machines.lean:912`, copies in `SimulatorNumeric.lean:503`
    and sc-compose's `ComposeSecurity/Machines.lean:150`) with `BinArith.encWords_def`, undisclosed. **The post-merge
    addendum** extends it to #327's public `SequentialZK.encodeMsgs_eq_encWords` (`Composability/SequentialZK/
    Normalization.lean:40`), unledgered at the pin and now in the DL-49 extension. The pack re-check finds the two
    equal from the keyword to the end of the proof after renaming bound variables (`L`, `w` ↔ `h`, `m`), with different
    docstrings: the same statement and proof, which the addendum and the DL-49 extension call verbatim copies.
- **Check the ledger rows against the code.** Do DL-51 and the DL-49 extension (at `67423db6`) name the right
  declarations, files and lines, and describe the relation correctly? `pack-checks/dupscan.txt` (§ *ledger rows against
  the code*) finds every cited declaration at its cited line (`Lengths.lean:83`, `Normalization.lean:40`,
  `DDH.lean:145`, `ThreeColoring/Machines.lean:912`; `StatisticalSwitch.lean:46` and `:68`, which DL-51 cites by file).
  Is any further undisclosed duplicate outside these rows?
- **Grade the SY-F05 remainder's proposed disposition** (ruling 10): is a ledger row with a re-point after #341 merges
  right, or should the pair be re-pointed onto #324's public lemmas before merge?
- The fixed and informational ones: SY-F04 (LE-doc), SY-F05 (LE-reuse; the remaining `OTAnswerWords` pair is ruling 10),
  SY-F06 (near-relatives: `ChunkScanner.scan` vs `Complexity.transduce`, `RunWithHost.acc` vs `StateLoop.MajLoop.acc`,
  `SliceReduction.distAdv_fibers_le` vs `OT.statClose_prod_of_forall`, `distAdv_chain_le` vs `abs_sub_le_sum_hybrids`),
  SY-F08 (inline getD/`List.ofFn` rewrites; the review counts 14 in 10 helpers; a line count finds
  `List.getD_eq_getElem` on 29 code lines in 16 helpers, 11 followed within three lines by `List.getElem_ofFn`, and
  **no** new theorem of the DL-47 shape, `dupscan.txt`). Are these dispositions right, and is any of them in fact a
  major?
- **Name interaction with #327/#324** (`pack-checks/names.txt`): no full-name clash with any TCSlib declaration at
  `201bf57a`; four short names occur on both sides in different namespaces: the addendum's three
  (`encodeMsgs_eq_encWords`, `exists_simulator`, `length_answersB`) and `outV_eq` (`TwoMoveViews.outV_eq` against #327's
  `Composability.PaddedVerifierSpec.outV_eq`; `Protocol.outV_eq` already existed at the tip). No sc-yao private name
  clashes, and no public helper shadows one of `Yao.lean`'s four private names.
- The review's own searches: `dup/` (namespace-resolved name scan of 764 new names; normalized-statement matches against
  21,045 tip theorem headers: 0 exact, 5 loose) and the interim review § *Duplication*.

**5. Rule 10**
- **Seals** (the review's own, whole-file over the full TCSlib import closure, `-DmaxErrors=0`, both error forms,
  install and EOF records; recounted from the raw logs in `pack-checks/rule10.txt`):
  - `Yao.lean`: **seal A 0** in both variants (3046/3047 requests); **seal B 24** in both, in 9 declarations, against 15
    in 8 at the tip (sc-garble's review seal of the same `Yao.lean`, with 1985 requests over the smaller closure without
    the hub; `rule10.txt`). The 9 new errors are
    `yaoHybrid_polyTime` 2 and `yaoHybrid_simulators` 7; the review read each and attributes all to `PolyExpr.eval`
    index or type conversions or cascades from them (`phase2/yao-B-attribution.txt`; the worker's
    `subagents/final-seal-attribution/`). `pack-checks/rule10-errors.txt` lists every error with its message and
    enclosing declaration. Is that attribution right, and is none a foreign-definition unfold?
  - `Uniform.lean`: **4** errors in every variant, in `DAGCircuit.length_encode_le_of_isFaninTwo` and
    `IsPUniform.isPolySize`; the tip's `Uniform.lean` sealed with the same 135 requests gives the same 4 in the same 2
    declarations (inherited; the readers pass). `DAGCircuit.lean`: 0 requests, 0 errors.
  - **Helpers: coe-A 68/68** (the hub and 67 children) with 0 errors; the three other variants sampled on five helpers
    (`CoinSeedRelabel` after LE-reuse, `Lengths` with its `nestedSpecial` match reduction, `Decryption`,
    `SliceReduction`, `GarbledRun`): 15/15 with 0 errors. The worker's own 272 helper seals (68 × 4 variants) have 0
    errors (`rule10/delivered-seal-recount.txt`). Is the sample adequate given the delivered 272?
- **Paired controls** (`mkctl_sy.py`; rows `PolyExpr.eval`, `DAGCircuit.IsFaninTwo`, the four SY-3 encodings, `spEncStr`,
  `Good`, the `FinDist` coercion, and the helper definitions `ChunkScanner.scan`, `RunWithHost.acc`,
  `CoinRelabel.keyRelabel`, `SelectedRows.offset`): coe 30 probes ALL_OK, 83 sealed negatives each failing exactly once,
  15 unsealed probes passing; strict 34 probes, 100/100 sealed negatives failing once, 17/17 unsealed passing, the only
  other failures `ctlCoeReader` in the 17 sealed probes (the harness effect of sc-ot F-09 and sc-garble).
- **Explicit-unfold scan** (Phase 1, `rule10/unfoldscan.txt`): 1512 tactic references, 28 short-name candidates, all local
  `let`/`have` names: **0 foreign**. The worker's scan and its resolution are under `worker/final/evidence/unfold/`.
  Does any proof read a foreign definition other than through a published reader, in particular `garbledTable`,
  `evalGate`, `Good`, `nestedSpecial`, `spEncStr`/`spDecStr`, `sliceEnc`, `sliceMultiEncDist`, the samplers,
  `Strategy.Efficient`, `View.encode`, `IsFaninTwo` and the circuit encodings?

**6. The rules and the evidence**
- **Docstrings:** does every new public declaration state its formula in Lean argument order, with a source tag where it
  comes from the source? The re-check (`pack-checks/docs.txt`) finds docstrings on all 739 new public declarations (the
  three attribute-placement cases included). The review's pre-LE-doc audits are `docs/docaudit.tsv`,
  `docs/docaudit2.tsv` and `docs/docclass.txt`.
- **Sketches:** every proof of 15 lines or more carries a `**Proof sketch.**` (the re-check: 64 new theorems, 0 without;
  the review's `docs/sketchaudit.txt` lists 4 long `rfl` statements as false positives). SY-F09: six proofs of 40 lines
  or more have no step comments, among them the 128-line `yaoHybrid_polyTime` body (`docs/stepcomments.txt`); graded
  info by the review. Do the two targets' sketches describe the delivered proofs?
- **Sources (no fabricated tags):** the tags are [PS10] (68 files), [LP09] (10), [BMR90] (4), [AB09] (4), [Gol04] (2) and
  [Gar26] (2) (`pack-checks/sources.txt`). There is no curated PS10 chapter-6 transcription in
  `blueprint/src/references/` at the pin (chapters 2–4 and the appendix only), so `sources.zip` `PS10/` gives §6.2 from
  the PDF at the pin (pages and text); every numbered PS10 locator used (Definition 155.1, Algorithm 157.2,
  Protocol 162.6, Theorem 163.7, §6.2.1, §6.2.3) is found there, and "Claim 157.a", "Construction 158.a", "Claim 159.a"
  are the inventory's labels for unnumbered text (`inventory-ch5-8.md`), as elsewhere in the library. [LP09], [BMR90],
  [Gol04] and [Gar26] have no transcription at the pin. Two file-level gaps found by the re-check, not recorded by the
  review: `ChunkScanner.lean` cites [AB09, §6.2] but its `## References` has no [AB09] entry, and
  `GarblingProgram.lean` cites [BMR90] but its `## References` lists only [PS10]. Is any tag or locator fabricated or
  wrong?
- **Evidence completeness** (G20-01): the delivery's `SHA256SUMS` (7597 rows) and `evidence/SHA256SUMS` (7515) verify
  against every blob of the final delivery, with exact path sets (`pack-checks/manifests.txt`); the review's ZIP has
  1511 entries = its 1510 manifest rows plus `SHA256SUMS`, all verified, its records copy equal. Is any evidence the
  claims need missing?

**7. The merge interaction (not an audit item)**
- `git merge-tree --write-tree` of the head with the pin, with `201bf57a` and with each open PR on the records branch
  (#331, #338, #339, #340) is clean and shares no path (`pack-checks/mergetrees.txt`). 145 modules are downstream of the
  PR at the head (75 outside it).
- **Pending merge condition.** The integration build of the head merged with the current tip (#327 and #324,
  `201bf57a`) is running separately; the maintainer runs it, and with #324's `hbcSecure_compose` proved,
  `yaoProtocol_hbcSecure` is expected to use only the standard axioms. Treat it as a condition on the merge. What you
  can raise: a concrete reason a merged tree cannot build, or a name or instance interaction.

## Known dispositions (not findings)

- **SY-F01** confirmed; **SY-F02** DL-51; **SY-F03** DL-49 extended (`67423db6`). **SY-F04** fixed by LE-doc;
  **SY-F05** fixed by LE-reuse (the remaining `OTAnswerWords` pair: ruling 10, open); **SY-F06** ledger note;
  **SY-F07** none (as SG-F07); **SY-F08** the DL-47 cleanup may re-point them; **SY-F09** cleanup (also the
  unnecessary `simpa` warning at `BobIO:211`); **SY-F10** the SY-4 host and promotion requests (H-SY-decoder,
  H-SY-eval, draft registry rows in REPORT § *Hosts*), a maintainer decision at the gate; **SY-F11** a note for DW-1;
  **SY-F12** the size exception (1179 ≤ 1,200, the lint's only new WARN).
- **The worker was Codex with three sub-agents** (SY-6); REPORT § *Contributions and ownership* records who proved what.
  The worker commits carry Seyoon's authorship.
- **The review's evidence ZIP is not copied into `verification.zip`** (19 MB): a pointer gives its committed path,
  size and SHA-256 at the pin, and every entry this pack cites is copied, each checked against the manifest. The ZIP's
  `landing/series/0009`–`0011` patch files are not copied (the commits themselves are on the PR branch).
- **The final review supersedes the interim review** (`9902d727`, "Phase 1 and landing prep"), which keeps the Phase 1
  detail the final review refers to (scope controls, layout, duplication, the delivered seal recount, the host log); it
  is in `verification.zip` (`records-history/`) and the bundle.
- **Counting differences:** the review counts admissions over the issued order plus the helpers (23 at the tip → 21 at
  the head); the re-check counts every TCSlib declaration with a `sorry` outside comments (550 → 548) and finds exactly
  the two targets removed and none added (`pack-checks/sorries.txt`). The review speaks of "eight SY-3 readers" for the
  delivery (`isFaninTwo_iff` and the seven in `Uniform.lean`); the PR adds seven.
- The PR description abbreviates `Complexity/CircuitComplexity/Uniform.lean` as `Circuits/Uniform.lean`.

## Also check

**Axioms** (review § *Axioms*; `landing/census-head.log` = `phase2/probe-runs/mods/ScYaoProbe_AxiomsLand.log`,
`landing/axioms-summary.txt`; built on `f9fda8fe`, before #324 merged):
- `yaoHybrid_polyTime`, `yaoHybrid_simulators`, `yaoHybrid_hbcSecure` and `yaoSeed_good_whp` print
  `[propext, Classical.choice, Quot.sound]`; their closures (9168, 20202, 20475, 17757 constants) have no direct
  `sorryAx` user. `yaoProtocol_hbcSecure` reached `sorryAx` only through `HybridProtocol.hbcSecure_compose` (#324, then
  unmerged); `otProtocol_*` are standard.
- The 1492 stored constants of the 71 owners are all standard; the SY-3 readers use no axioms. No user `@[simp]`: the
  only new simp-tagged constants are the generated `FakeSimulator.Data.mk.sizeOf_spec`/`injEq`; the three `@[simps …]`
  attributes all set `isSimp := false` (`pack-checks/docs.txt`).

**Admissions:** at the head no sc-yao module has a `sorry`; `Yao.lean` has none.

**Sizes and widths:** `Yao.lean` 1179 (SY-2), every other file at most 1000 lines, every line at most 100 characters
(`source-head.json`, `pack-checks/docs.txt`).

**Build** (review Phase 2, `dl-oleans-2`, one Lean process, `scripts/lean_check_tree.sh` only): incremental from the
tree's snapshot base `eff2dcd0` by import-closure keys, **718/718 modules rc 0, 0 `error:` and 0 `error(`**, no log
containing "error"; the whole downstream of `eff2dcd0..e9b03c43` (145 downstream of sc-yao), root `TCSlib`,
`audits/pass-shelat/Checks` and `audits/garg-ch1-3/Checks` (`landing/build-summary.txt`, `landing/root-checks.jsonl`).
Whole-order state check 1356/1356 OK (`landing/tree-check-head.txt`). sc-yao's modules: no `sorry`, one linter warning.
Restore: `dl-oleans-2` back to snapshot `457ba704…`.

**Lint** (line sets, tip → head): Cryptography 92/101 → 92/102, the only new line `Yao.lean`'s size WARN (SY-2);
Complexity 25/390, `Uniform.lean`'s check-8 WARN loses `encodeList`; no new FAIL (`lint/linediff-*.txt`).

## Evidence

- **`review.md`**, **`post-merge-addendum.md`** (records pin, `fills/sc-yao/final-r1/`): the maintainer's delivery
  review, verdict ACCEPT WITH LANDING EDITS (SY-F01–SY-F12), and the addendum after #327 and #324 merged.
  **`rulings.md`** (`fills/sc-yao/final-r1/`, records commit `67423db6`): Seyoon's rulings on SY-F01 to SY-F03.
- **`verification.zip`** (249 entries): every file the pack cites, as byte-identical originals except four generated
  ones. Its `SHA256SUMS` lists every other entry, and `PROVENANCE.txt` gives each entry's source. It holds:
  - `review-evidence-SHA256SUMS` (the review ZIP's manifest, 1510 rows) and `review-evidence-POINTER.txt` (the ZIP at
    `fills/sc-yao/final-r1/review-evidence.zip`, 1511 entries, SHA-256
    `d3f7c3da0d081acd9275e798514fffd7b538c83787a109c11c59bab4e2c3b5a8`, not copied);
  - `landing/PROVENANCE.txt`: the review's PROVENANCE (= the ZIP's);
  - `evidence/` (141): byte copies of the ZIP entries this pack cites (integrity, landing, scope, layout, docs, dup,
    rule10, lint, host, admissions, the Phase 2 build, axioms, seals, controls and restore summaries, the frozen files'
    seal logs and probe sources except `Yao.lean`'s 3.3 MB seal logs, and the review's tools);
  - `records/` (29): the issue package `fills/sc-yao/issued-r1/`, the final review and addendum, the decision log, the
    duplication ledger, deferred work, the inventory, policy, the secure-computation plan, the S3b design notes, the
    host addendum, Gate 27's findings and resolutions, Gate 36's findings and resolutions, ruling SG-1 and
    `sources.json`, at the pin; `records-history/9902d727/`: the interim review; `records-after-pin/67423db6/`: the
    rulings, the ledger and the deferred-work register at the rulings commit;
  - `worker/final/` (40): byte copies from exchange `47c38c479e4be52654cd2c055141dfb64be975c4` (`inbox/fills/sc-yao/`):
    REPORT, `SHA256SUMS`, `COMMITS.tsv`, the worklog, the scope requests, the final header check and its controls, the
    reader manifest, the clash scan, the unfold scan and its resolution, the final seal and audit summaries, the seal
    attribution sub-agent's report and excerpts, the common-contract disclosures and the source inventory;
  - `context/` (8): `Normalization.lean`, `ComposeSecurity/Lengths.lean`, `ComposeSecurity/Machines.lean`,
    `ComposeSecurity.lean`, `Candidates/DDH.lean`, `ThreeColoring/SimulatorNumeric.lean`, `ObliviousTransfer/ViewA.lean`
    and `YaoReal.lean`, at `201bf57a`;
  - `pr/`: the PR description and the REST fields the re-checks read;
  - `pack-checks/` (20): the re-checks for this pack, from git objects only (no Lean), with their scripts.
- **The worker's own evidence:** on the exchange at `47c38c47`, under `inbox/fills/sc-yao/` (7598 files).
- **`landing/`:** byte copies of evidence-ZIP entries: `build-summary.txt` (= `phase2/build-head/summary.txt`),
  `root-checks.jsonl` (= `phase2/build-head/results.jsonl`), `tree-check-head.txt` (= `phase2/build-head/statecheck.txt`),
  `census-head.log` (= `phase2/probe-runs/mods/ScYaoProbe_AxiomsLand.log`), `axioms-summary.txt`
  (= `phase2/axioms-summary.txt`), `frozen-check.txt` (= `landing/yao-scope-vs-tip-final.txt`) and `uniform-check.txt`
  (= `landing/uniform-scope-vs-tip.txt`).
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `47c38c47`.
- **`pr-description.md`:** the PR #341 description, read with the GitHub MCP tools on 2026-11-16 (`.body`, raw; equal
  byte for byte to the REST API's).
- **`pr.diff.txt`:** `git diff` from the merge base to the head (70 paths, 15813 insertions, 67 deletions).
- **`source-head.json`:** the head, base and pin, and the hashes, line counts and over-width counts of the 70 files.
- **`sources.zip`:** the source closure at the head of every changed module (`TCSlib/`, 262 files), and `PS10/`: [PS10]
  §6.2 (book pages 154–164) from `Pass–Shelat.pdf` at the pin, as the PDF pages and as `pdftotext` text, with a README
  locating each cited item.
- **The bundle** has the rulings and the ledger and deferred-work register at `67423db6` (in place of the pin's), and
  adds, as context at the head: `SecureComputation/Defs`, `Hybrid`, `Garbling`, `GarblingSpecial`,
  `SpecialEncryptionMulti` (B1) and `YaoReal`; and at `201bf57a`: #327's `SequentialZK/Normalization` and #324's
  `ComposeSecurity/Lengths`.

## Findings delivery

Return `gate42-sc-yao-findings.md` as a Markdown file in this chat. If you have several evidence files, return a ZIP.
The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope
  violation.
- **major:** a changed frozen statement, a forbidden read in a touched declaration not covered by the rulings, an
  undisclosed copied private lemma or undisclosed re-proof of a public one outside the ledger rows and rulings in force,
  a fabricated source tag, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, proof sketch or citation.
- **note:** anything else.

Grade SY-F01 to SY-F12 in a separate table (agree, or regrade with the reason). Report the audited head and the counts by
severity. The gate closes at zero blockers and zero majors.
