## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/pack-r2.md =====

# Gate 20 · Duplication consolidation DL-30–DL-34 · round 2

The auditor is Codex. Round 1 was HOLD (0/1/1/0); its findings are `findings/gate20-dl-consolidation-findings.md`.
This round re-audits the two fixes and the one new commit. The round-1 pack (`pack.md`) still defines the scope; its
questions stand for anything round 1 left unverified.

- **PR:** draft [PR #298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), now at
  `c2839c41ca6b3a9c34db1595a1ad287768316630` (tree `5eb486b8c2f1901e3c4db08b610840a12d13fe0f`).
- **Base:** `2ea4df08d009a4bbdb8042795ff062d7f22db325`, unchanged. Later base commits touch records only.
- **New since round 1:** one commit, **LE-gate20** `c2839c41`, on top of the round-1 head `6f853adc`.
- **Resolutions:** `resolutions-r1.md`.

## What to check

### 1. G20-01: is the raw evidence now complete?

**`supplement-r1/verification-supp.zip` and `landing-supp.zip`**
- They hold the 1028 and 92 files that `verification.zip` and `landing.zip` left out.
- Each file should be byte-identical to the hash in its main ZIP's inner `SHA256SUMS`.
- Main plus supplement should cover 2441/2441 and 188/188 entries. `supplement-r1/coverage-check.txt` records this.
- Please confirm, and check what the files show:
  - the baseline and head census and collector runs;
  - the 80 base and 82 head whole-file seal logs and their `results.jsonl`, with the seal sources, manifests and
    request records;
  - the control plan and sources, and the 22 nm-sim seal runs.
- Do the raw runs support the seal table (A 34/41, B 30/41 at head; 33/40, 28/40 at base; 0 new failing
  declarations), the census (2112 → 2099) and the nm-sim 22/22?

**Do the seals cover the final landing?** Your round-1 note said the worker's seal corpus predates the landing
edits. `resolutions-r1.md` § G20-01 explains why the maintainer's seals, together with the later re-seals, cover
`c2839c41`:
- the head seals were taken at `8e43131f`;
- LE-rule10's three modules were re-sealed at `7b7d07aa`;
- the 11 nm-sim files were sealed at `6f853adc`;
- LE-gate20's two files were re-sealed at `c2839c41`;
- the closure check covers the #297 rebase.

Is that argument sound?

### 2. G20-02 and LE-gate20

The diff is `landing-r1/LE-gate20.patch`, 2 files.

- **`UniversalPadding.lean`:** the private `PadQuad.ofFn_arrowCongr` is deleted. Its two uses rewrite with
  `ofFn_arrowCongr_finCongr`.
- **`OneWayLemmas.lean`:** `OneWay.ofFn_block_eq_take_drop` keeps its statement byte for byte. Its proof is
  `FunFamily.ofFn_blocks` through `FunFamily.blocks_apply`, with no unfolding of `blocks` or `blocksEquivX`.

Check that:
- the statement is unchanged;
- the proof uses only published lemmas;
- no other copy that the round-1 audit named remains.

**Evidence** (`landing-r1/`): `gate20-r1-evidence.zip` and its manifest `evidence-SHA256SUMS`. Nothing is left
out: the ZIP's entries are exactly the manifest's paths. Extracts:
- **Build:** 114 downstream modules through root `TCSlib` and both `audits/*/Checks` were rebuilt, all rc 0.
  `final-tree-check.txt` shows all 1198 modules with rc 0 at the head's source hashes.
- **Statements:** decls2 over the two files gives 0 rows. The whole PR is still 68/42/2/0.
- **Axioms:** the 164 constants of the two files are standard, and so are the 16 endpoints
  (`axioms-summary.txt`).
- **Seals:** see `seal-compare.txt`.
  - `OneWayLemmas` passes A and B, both at the head and at `6f853adc`.
  - `UniversalPadding` fails at the same 4 (A) and 5 (B) untouched declarations at the head and at `6f853adc`. It
    is not in the 41-file table.
  - 0 new failing declarations.
  - Paired controls ALL_OK.
- **Lint and widths:** lint shows an empty diff, and no line is newly over 100 characters (`widths-sizes.txt`).

## Updated files

- **`pr.diff-r2.txt`:** `git diff` from the base to `c2839c41`, over 53 paths.
- **`source-head-r2.json`:** hashes, line counts and over-width counts for the 52 changed files, and the 1 deleted
  file.

## Findings delivery

Return `gate20-dl-consolidation-r2-findings.md` as Markdown in this chat. If you have several evidence files, return
a ZIP. Use the same table and severities as round 1, and say for each round-1 finding whether it is closed. Report
the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/resolutions-r1.md =====

# Gate 20 · resolutions, round 1

The round-1 verdict was HOLD, with counts 0 blockers, 1 major, 1 minor and 0 notes.
- **Findings:** `findings/gate20-dl-consolidation-findings.md` (SHA-256
  `d2938faf2840295cdc57560c748af301af1a8fb219dd8d30637cdd06b8fc4282`).
- **Audited head:** `6f853adc61d5d175ee83c69f6c07ab2da112cabc`.
- **New head:** `c2839c41ca6b3a9c34db1595a1ad287768316630`, tree `5eb486b8c2f1901e3c4db08b610840a12d13fe0f`.
  Its one new commit is LE-gate20.

| # | Severity | Disposition |
|---|---|---|
| G20-01 | major | **Fixed (evidence only).** The two supplements are in `supplement-r1/`. |
| G20-02 | minor | **Fixed** by **LE-gate20** `c2839c41`. Evidence: `landing-r1/`. |

## G20-01

`supplement-r1/` holds `verification-supp.zip` and `landing-supp.zip`.
- **Contents:** the 1028 and 92 omitted files. Every one is the original, byte-identical to the hash in its ZIP's
  inner manifest. Nothing was re-run.
- **Coverage:** the main ZIP and its supplement together cover every manifest entry: 2441/2441 and 188/188, with
  every hash matching, no overlap, and nothing outside the manifest (`supplement-r1/coverage-check.txt`).
- **The examples the finding names are all present:**
  - the base census and collector logs;
  - both `results.jsonl` files for the base and head seal runs;
  - the 80 base and 82 head seal logs;
  - `controls/out/controls-plan.json` and the control sources;
  - the 22 nm-sim seal logs;
  - `seals/{A,B}/manifest.json`.
- **The new evidence for LE-gate20** (`landing-r1/gate20-r1-evidence.zip`) leaves nothing out: `unzip -Z1` lists
  exactly the paths of its manifest `evidence-SHA256SUMS`.

**The 41-file seal table and the final landing.** Codex notes that the worker's seal corpus predates the landing
edits and the #297 rebase. The maintainer's head seals in `verification.zip` and its supplement already cover the
landing edits:
- the head seals were generated at landing head `8e43131f`;
- the three LE-rule10 modules were re-sealed at `7b7d07aa`.

Each later change touches only modules whose own seals were re-run:
- **#297 rebase:** none of the 41 sealed owners has a file or TCSlib closure containing a changed module
  (`landing.zip:logs/consolidation-seal-closure-check.txt`). The 11 nm-sim files were sealed at `6f853adc`.
- **LE-gate20:** it changes only proofs in its two files, which were re-sealed at `c2839c41`. A proof change in a
  dependency does not affect another file's seal: seals make foreign definitions opaque, and a theorem's proof is
  never unfolded.

## G20-02 · LE-gate20 (`c2839c41`)

The diff touches 2 files, +9 −17 (`landing-r1/LE-gate20.patch`).

**`Asymptotic/UniversalPadding.lean`**
- The private `PadQuad.ofFn_arrowCongr` is deleted.
- Its two uses, in `ofFn_appendEquiv` and `ofFn_splitCoins_symm_cast`, now rewrite with
  `ofFn_arrowCongr_finCongr`.

**`Asymptotic/OneWayLemmas.lean`**
- The statement of `OneWay.ofFn_block_eq_take_drop` is byte-identical.
- Its proof is now `FunFamily.ofFn_blocks`, read through the published `FunFamily.blocks_apply`. It unfolds neither
  `blocks` nor `blocksEquivX`.
- The docstring gains a proof sketch.

## Checks at `c2839c41`

These are in `landing-r1/`, and the raw runs are in `gate20-r1-evidence.zip`.

**Build**
- The two files and everything downstream were rebuilt on the consolidation's full tree: 114 modules through root
  `TCSlib` and both `audits/*/Checks`, all with rc 0.
- All 1198 TCSlib/`audits` modules end with rc 0 at the final-head source hash, with 219 admission warnings
  (unchanged).

**Statements** (re-run by the maintainer)
- decls2 over the two files from `6f853adc`: 0 rows.
- Whole PR from `2ea4df08`: 68 ADDED / 42 REMOVED / 2 MOVED / 0 CHANGED, unchanged.

**Axioms**
- The 164 stored constants of the two files are standard.
- `ofFn_block_eq_take_drop` and `length_take_drop_block` print `[propext, Classical.choice, Quot.sound]`.
- The 16 endpoints are unchanged.

**Rule 10**

| File | A, head vs `6f853adc` | B, head vs `6f853adc` |
|---|---|---|
| `OneWayLemmas` | pass, pass | pass, pass |
| `UniversalPadding` | fails at the same 4 declarations (`exists_family`, `family_inLen`, `invProbAt_family_le`, `lengthRegular_gStr`) | fails at the same 5 declarations (those 4 and `strongOneWay`) |

- These failures predate this PR: neither file is in the consolidation's seal table, and none of the failing
  declarations is touched.
- New failing declarations: 0.
- Paired controls: ALL_OK for both files. Every sealed negative fails exactly once.

**Lint:** an empty diff against `6f853adc`.

**Sizes and widths:** 909 and 522 lines; no new line over 100 characters.

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/findings/gate20-dl-consolidation-findings.md =====

# Pass–shelat Gate 20 — external Codex audit

**Verdict: HOLD.** Counts: **0 blockers, 1 major, 1 minor, 0 notes**.

The source review found no audited statement drift or demonstrated mathematical defect. The gate remains open because required raw verification evidence is missing. Two small, eligible duplication folds also remain.

## Pins and scope

- Repository / draft PR: [Shilun-Allan-Li/tcslib #298](https://github.com/Shilun-Allan-Li/tcslib/pull/298).
- Audited Lean head: `6f853adc61d5d175ee83c69f6c07ab2da112cabc`.
- PR base: `2ea4df08d009a4bbdb8042795ff062d7f22db325`.
- Campaign records: `3015c622434a0321e784a3da1d83c125b426bf7e`.
- Exchange / pack: `1350b6083bb08760ab32ada31da63a860377c7f9`, `outbox/gates/20-dl-consolidation-gate/`.
- Scope: DL-30–DL-34 promotions, deletions and uses; all five landing edits, including the #297 re-points. Deferred DL-36/DL-37 work is excluded, apart from the explicitly landed deletion.

## Findings

| ID | Severity | File / declaration | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G20-01 | **major** | `verification.zip`, `landing.zip`: baseline census, whole-file seals and paired-control evidence | The archives omit necessary raw evidence, beyond the documented omission of generated seal sources. `verification.zip` omits **80 baseline and 82 initial-head seal logs**, their run records, the baseline census/collector logs, and the review control plan/sources. `landing.zip` omits **all 22 nm-sim seal logs**, their run records, and the seal request records/manifests. These files are named and hashed in the inner manifests but absent from the ZIP entries. No loose counterparts occur in the pinned final-delivery paths. Consequently the reported whole-file coverage, baseline comparison and 22/22 nm-sim seal result cannot be checked from their raw runs. The three final re-sealed modules and the separately supplied nm-sim paired controls do not supply those missing runs. | Supply the missing baseline/head census and seal request records, instrumented sources or reproducible generation inputs, raw logs and `results.jsonl`, plus the review control plan/sources. Include both seal variants and update the pack manifests. Existing originals matching the recorded hashes suffice; rerun only evidence that cannot be recovered. |
| G20-02 | **minor** | `Asymptotic/UniversalPadding.lean:180`, `PadQuad.ofFn_arrowCongr`; `Asymptotic/OneWayLemmas.lean:75`, `OneWay.ofFn_block_eq_take_drop` | Two disclosed copies have straightforward folds that the delivery review’s “Debt now foldable” list misses. The private `ofFn_arrowCongr` has the same statement as promoted `ofFn_arrowCongr_finCongr`, and retains two uses at lines 190 and 199. The public block-window theorem still re-proves the new `FunFamily.ofFn_blocks` result. Worker §11 says that relating the functions would require unfolding; the published `FunFamily.blocks_apply` reader supplies that relation. Both files already depend on `Adversary`; neither fold needs an import cycle or an audited statement change. | Delete the private width-cast copy and re-point its two uses. Preserve the public block-window statement and derive its proof from `FunFamily.ofFn_blocks` through `FunFamily.blocks_apply`. Rebuild the affected consumers. |

Concrete missing-file examples for G20-01:

```text
verification.zip:
  base-census-run/mods/DlProbe_CensusBase.log
  base-probe-runs/mods/DlProbe_CollectBase.log
  base-seal-runs/results.jsonl
  base-seal-runs/mods/DlProbe_BaseSeals_BaseSealA_Cryptography_Asymptotic_Adversary.log
  seal-runs/results.jsonl
  controls/out/controls-plan.json
landing.zip:
  seal-runs/results.jsonl
  seals/A/manifest.json
  seals/B/manifest.json
```

The omissions inventory and all 184 missing active seal-log paths are in the accompanying evidence. The old worker seal corpus predates the landing edits and #297 rebase; it does not certify the final landing.

## Independently checked

1. **Integrity.** All **17/17** outer SHA-256 entries match, including all three ZIPs. Included inner-manifest files also match: **1413** in `verification.zip`, **96** in `landing.zip`, and **4/4** in `statements-r2/`. The respective main inner manifests additionally name **1028** and **92** omitted files. Both evidence ZIPs are the same Git blobs as their pinned campaign-record counterparts.
2. **Source identity.** All **240** source-closure files match Git blobs at the audited head. All **50** `source-head.json` hashes match. A freshly generated Git diff is byte-identical to `pr.diff.txt` with `--abbrev=9`: **51 paths**, **1471 insertions**, **1469 deletions**.
3. **Statement freeze.** Re-running the supplied textual declaration comparison gives **68 added, 42 removed, 2 moved, 0 changed** public headers. A separate byte comparison passes for **all 16 named endpoints**, including `padded_cpa` across its file move, and for `castImpl_snmImpl` and `castImpl_indImpl_abs`. Context and name-resolution changes were also reviewed. This does not replace the missing elaborated baseline census.
4. **Landing edits.** LE-split moves `section PaddedCPA` byte-for-byte at its commit. LE-review changes only comments/whitespace in six files. LE-rule10 replaces the exposed OracleSecurity body reads with published readers; the six available final seal probes for PaddedCPA, BitwiseCPA and TrapdoorCPA have source/probe hashes matching the supplied files and final sources. The #294/#297 changes reviewed are consistent with their name re-points, removed selective opens, wrapping, and the one DL-37 deletion.
5. **Promotions.** Reviewed the probability, simulation, codec, block, list and handler APIs against their deleted forms. The two S1 forms have different hypotheses and appropriately remain separate. P2 is a corollary proved through `Bridge.expect_sample_pair`. R3 retains arbitrary initial state through explicit casts and specializes to the deleted BitwiseCPA form at `none`. R5 retains the constant-answer theorem as a specialization. R7’s statement-freeze escalation is justified.
6. **Build/axiom evidence.** All **15** supplied final rebuild records have `rc = 0`, zero errors and source hashes matching Git. The aggregated build records have **1229** latest module records with no failed latest run; all **240** source-closure hashes match their latest build records. The available head censuses contain **2099** consolidation constants and **572** nm-sim constants; only the four identified Yao constants use `sorryAx`, and nm-sim’s census has none. The 16 endpoint axiom prints list only `propext`, `Classical.choice`, `Quot.sound`.
7. **Controls and policy.** Rechecking the supplied nm-sim control plan against its raw logs gives **8/8** expected probe outcomes, including **38** sealed negative controls. **1297** available latest result/log hash pairs match. The 240-module TCSlib source import closure is complete and acyclic. No new `@[simp]` appears; line/width counts match the manifest, with no per-file increase in over-width lines. ElGamal remains the inherited size exception. The recorded lint delta and deferred DL-36/DL-37 items are not additional findings.

## Verification boundary

This audit independently checked source, Git objects, hashes, declaration text and available raw evidence. **No fresh Lean elaboration was performed.** Build and axiom results above describe the supplied, checked records. Full Rule-10 closure and elaborated baseline-census claims remain unverified for the precise omissions in G20-01.

The user dispatches and merges. No repository changes, review submission, push or merge was made.

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/supplement-r1/README.md =====

# Gate 20 · supplement r1 (G20-01)

These are the raw evidence files that `verification.zip` and `landing.zip` left out for size. Each one is the
original, byte-identical to the hash recorded in that ZIP's inner `SHA256SUMS`. Nothing here was re-run.

| Archive | SHA-256 | Files | Completes |
|---|---|---|---|
| `verification-supp.zip` | `5a219acc27e4cb05ecc653af408895a30cd405bafe329a14fcc7863a872d8a72` | 1028 | `verification.zip` (inner manifest `35bfc608…`, 2441 entries) |
| `landing-supp.zip` | `b234696208975c9f14057ce379f458075fe6c5a2be42fe7e68cceabd7c213ed0` | 92 | `landing.zip` (inner manifest `da4ad8b3…`, 188 entries) |

**Paths.** Entry paths are relative to the same root as the main ZIP: the review directory and the rebase-r1
directory respectively. Unzip each supplement over its main ZIP.

**`coverage-check.txt`.** It confirms that the main ZIP and its supplement together hold every manifest path. Every
hash matches, there is no overlap, and the supplement holds nothing outside the manifest.

## What `verification-supp.zip` holds (by top-level directory)

| Directory | Files | Content |
|---|---|---|
| `base-census-run/`, `base-probe-runs/` | 3, 5 | the baseline census and collector runs and logs |
| `base-seals/`, `base-seal-runs/` | 162, 82 | baseline whole-file seal sources, manifests and request records; raw logs and `results.jsonl` |
| `seals/`, `seal-runs/` | 166, 84 | head seal sources, manifests and request records; raw logs and `results.jsonl` |
| `controls/` | 118 | the paired controls: `controls/out/` (the control plan and the 34 generated control sources, sealed `ControlS` and unsealed `ControlU`), `controls/records/` (82 seal request records) and `controls/controls-result.json` |
| `probe-sources/` | 7 | the census and collector probe sources |
| `base-tree/`, `base-tree-extra/` | 231, 4 | the baseline olean-tree build: per-module raw logs and `results.jsonl` |
| `superseded/` | 166 | runs replaced by later ones and kept for completeness: paired-control attempt 1, and the probe runs before and during LE-rule10 (`superseded/DISPOSITION.txt` gives each one's disposition) |

## What `landing-supp.zip` holds

| Directory | Files | Content |
|---|---|---|
| `seals/` | 46 | the 22 nm-sim seal sources for variants A and B, with `seals/{A,B}/manifest.json` and the request records |
| `seal-runs/` | 24 | the 22 raw seal logs and `results.jsonl` |
| `controls-records/` | 22 | the 22 nm-sim seal request records that the paired controls are built from |

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/supplement-r1/coverage-check.txt =====

verification.zip + verification-supp.zip: manifest 2441 entries (incl. SHA256SUMS self-entry: False); main zip files 1414; supplement 1028; overlap 0; hash OK 2441; mismatched 0; still missing 0; supplement files not in manifest 0
landing.zip + landing-supp.zip: manifest 188 entries (incl. SHA256SUMS self-entry: False); main zip files 102; supplement 92; overlap 0; hash OK 188; mismatched 0; still missing 0; supplement files not in manifest 0

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/landing-r1/LE-gate20.patch =====

commit c2839c41ca6b3a9c34db1595a1ad287768316630
Author: Claude <noreply@anthropic.com>
Date:   Fri Nov 13 06:01:05 2026 +0000

    dl-consolidation landing edit LE-gate20: fold ofFn_arrowCongr and ofFn_block_eq_take_drop (G20-02)
    
    Gate 20 minor finding G20-02, two folds the delivery missed:
    - Asymptotic/UniversalPadding.lean: the private ofFn_arrowCongr had the statement of the
      promoted ofFn_arrowCongr_finCongr (Asymptotic/Adversary.lean, A3). Deleted; its two uses
      (ofFn_appendEquiv, ofFn_splitCoins_symm_cast) rewrite with ofFn_arrowCongr_finCongr.
    - Asymptotic/OneWayLemmas.lean: OneWay.ofFn_block_eq_take_drop keeps its statement byte for
      byte; its proof is now FunFamily.ofFn_blocks read through the published FunFamily.blocks_apply
      (no unfolding of blocks or blocksEquivX). Docstring gains the proof sketch.
    
    Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
    Claude-Session: https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

diff --git a/TCSlib/Cryptography/Asymptotic/OneWayLemmas.lean b/TCSlib/Cryptography/Asymptotic/OneWayLemmas.lean
index 96ad2a9cc..0bb677c17 100644
--- a/TCSlib/Cryptography/Asymptotic/OneWayLemmas.lean
+++ b/TCSlib/Cryptography/Asymptotic/OneWayLemmas.lean
@@ -71,19 +71,16 @@ open Complexity Turing Finset
 /-! ### Blocks of a string -/
 
 /-- Block `i` of `x : Fin (q * ℓ) → Bool` (positions `ℓ·i, …, ℓ·i + ℓ - 1`) is the `ℓ`-bit window
-of `List.ofFn x` after `i·ℓ` bits. -/
+of `List.ofFn x` after `i·ℓ` bits.
+
+**Proof sketch.** The block is `FunFamily.blocks q ℓ x i` (`FunFamily.blocks_apply`), whose word is
+that window (`FunFamily.ofFn_blocks`). -/
 theorem ofFn_block_eq_take_drop {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
     List.ofFn (fun j : Fin ℓ => x (finProdFinEquiv (i, j))) =
       ((List.ofFn x).drop (i * ℓ)).take ℓ := by
-  have hle : i * ℓ + ℓ ≤ q * ℓ := by
-    have : (i + 1) * ℓ ≤ q * ℓ := Nat.mul_le_mul_right ℓ i.2
-    rwa [Nat.add_mul, Nat.one_mul] at this
-  refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
-  simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
-  congr 1
-  ext
-  simp only [finProdFinEquiv_apply_val]
-  ring
+  have hblk : (fun j : Fin ℓ => x (finProdFinEquiv (i, j))) = FunFamily.blocks q ℓ x i :=
+    funext fun j => (FunFamily.blocks_apply q ℓ x i j).symm
+  rw [hblk, FunFamily.ofFn_blocks]
 
 /-- The window of `ℓ` bits after `i·ℓ` bits of `List.ofFn x` has exactly `ℓ` bits. -/
 theorem length_take_drop_block {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
diff --git a/TCSlib/Cryptography/Asymptotic/UniversalPadding.lean b/TCSlib/Cryptography/Asymptotic/UniversalPadding.lean
index fcc6cc720..cd7319b55 100644
--- a/TCSlib/Cryptography/Asymptotic/UniversalPadding.lean
+++ b/TCSlib/Cryptography/Asymptotic/UniversalPadding.lean
@@ -176,18 +176,13 @@ theorem quadraticCode_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {
 
 /-! ## One-wayness of the padded family -/
 
-/-- `List.ofFn` through a `finCongr` relabelling of the index type. -/
-private theorem ofFn_arrowCongr {a b : ℕ} (h : a = b) (f : Fin a → Bool) :
-    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) f) = List.ofFn f :=
-  (List.ofFn_congr h f).symm
-
 /-- The encoding of a pair of strings assembled by `Fin.appendEquiv` (and a length cast) is
 the concatenation of the encodings. -/
 private theorem ofFn_appendEquiv {a b n : ℕ} (h : a + b = n) (q : (Fin a → Bool) × (Fin b → Bool)) :
     List.ofFn (((Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool))) q) =
       List.ofFn q.1 ++ List.ofFn q.2 := by
   show List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) (Fin.append q.1 q.2)) = _
-  rw [ofFn_arrowCongr, List.ofFn_fin_append]
+  rw [ofFn_arrowCongr_finCongr, List.ofFn_fin_append]
 
 /-- The encoding of a coin string reassembled by `splitCoins` (and a length cast) is the
 concatenation of the encodings of the halves. -/
@@ -196,7 +191,7 @@ private theorem ofFn_splitCoins_symm_cast {a b n : ℕ} (h : a + b = n)
     List.ofFn (((splitCoins a b).symm.trans (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool))) q) =
       List.ofFn q.1 ++ List.ofFn q.2 := by
   show List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) ((splitCoins a b).symm q)) = _
-  rw [ofFn_arrowCongr]
+  rw [ofFn_arrowCongr_finCongr]
   obtain ⟨q₁, q₂⟩ := q
   exact ofFn_splitCoins_symm a b q₁ q₂
 

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/landing-r1/seal-compare.txt =====

A Cryptography_Asymptotic_OneWayLemmas: head pass (install 1 eof 1); 6f853adc pass; new failing decls 0; head failing []
A Cryptography_Asymptotic_UniversalPadding: head FAIL 6e/4d (install 1 eof 1); 6f853adc FAIL 6e/4d; new failing decls 0; head failing ['TCSlib.Cryptography.PadQuad.exists_family', 'TCSlib.Cryptography.PadQuad.family_inLen', 'TCSlib.Cryptography.PadQuad.invProbAt_family_le', 'TCSlib.Cryptography.PadQuad.lengthRegular_gStr']
B Cryptography_Asymptotic_OneWayLemmas: head pass (install 1 eof 1); 6f853adc pass; new failing decls 0; head failing []
B Cryptography_Asymptotic_UniversalPadding: head FAIL 7e/5d (install 1 eof 1); 6f853adc FAIL 7e/5d; new failing decls 0; head failing ['TCSlib.Cryptography.PadQuad.exists_family', 'TCSlib.Cryptography.PadQuad.family_inLen', 'TCSlib.Cryptography.PadQuad.invProbAt_family_le', 'TCSlib.Cryptography.PadQuad.lengthRegular_gStr', 'TCSlib.Cryptography.PadQuad.strongOneWay']
neither file is in the consolidation 41-file seal table; comparison is against the same file at 6f853adc (old source sealed over the same closure)

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/landing-r1/axioms-summary.txt =====

census: 164 stored constants of OneWayLemmas + UniversalPadding
     53 [Quot.sound, propext]
     53 [Classical.choice, Quot.sound, propext]
     42 []
     16 [propext]
outside {propext, Classical.choice, Quot.sound}:
#print axioms:

'TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmSecure_of_simNMSecure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Composability.FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Composability.FixedLengthPKScheme.simNMSecure_cpa_iff_nmSecure_cpa' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OneWay.ofFn_block_eq_take_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OneWay.length_take_drop_block' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PadQuad.exists_pow_dominates' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PadQuad.length_gStr' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.PadQuad.lengthRegular_gStr' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.PadQuad.family_inLen' depends on axioms: [propext]
'TCSlib.Cryptography.PadQuad.ofFn_family_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.PadQuad.exists_linearTime_gStr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PadQuad.easy_of_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PadQuad.quadraticCode_of_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PadQuad.raw_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.PadQuad.gStr_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.PadQuad.padStr_eq_gStr' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.PadQuad.f_eq_of_gStr_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.PadQuad.invProbAt_family_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PadQuad.strongOneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PadQuad.exists_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Composability.prfFixedScheme_cpa' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Composability.prfFixedScheme_cca1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Composability.not_prfFixedScheme_cca2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Composability.prfFixedScheme_not_cca2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_rsa' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_factoring' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmSecure_cca2_of_indSecure_cca2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Composability.FixedLengthPKScheme.indSecure_cca2_of_nmSecure_cca2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Composability.FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/landing-r1/final-tree-check.txt =====

gate20 rebuild: 114 modules, rc!=0 [], errors 0
full order at head c2839c41 1198 modules (+31 PFR); missing []; rc!=0 or source differs from head: []
errors 0 sorry warnings 219

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/landing-r1/PROVENANCE.txt =====

dl-consolidation gate20-r1: landing edit LE-gate20 for Gate 20 finding G20-02 (2026-11-13 UTC)
worktree $SP/wt-land-dlcons, branch land/pass-shelat-dl-consolidation (local commit only; not pushed).
  parent 6f853adc61d5d175ee83c69f6c07ab2da112cabc (draft PR #298 head)
  head   c2839c41ca6b3a9c34db1595a1ad287768316630, tree 5eb486b8c2f1901e3c4db08b610840a12d13fe0f
  commit "dl-consolidation landing edit LE-gate20: fold ofFn_arrowCongr and ofFn_block_eq_take_drop (G20-02)"
  (landing/landing-log.txt, landing/0001-*.patch, landing/LE-gate20.diff). No rebase, no amend.
change: Asymptotic/UniversalPadding.lean: private PadQuad.ofFn_arrowCongr deleted, its 2 uses (ofFn_appendEquiv,
  ofFn_splitCoins_symm_cast) rewrite with ofFn_arrowCongr_finCongr (TCSlib.Cryptography, Adversary.lean).
  Asymptotic/OneWayLemmas.lean: OneWay.ofFn_block_eq_take_drop statement byte-identical; proof = funext through
  FunFamily.blocks_apply, then FunFamily.ofFn_blocks; docstring gains a proof sketch.
lean 4.25.0; olean tree $SP/dl-oleans only (one Lean process at a time; scripts/lean_check_tree.sh via tools/runner.py).
build: order/full/order.txt (tools/downorder.py at the head: 1198 modules + 31 PFR); order/delta (changed 2,
  downstream 114 incl. root TCSlib and audits/{pass-shelat,garg-ch1-3}/Checks); order/rebuild-queue.txt = stale or
  downstream (114). build/: 114/114 rc 0, 0 errors. logs/final-tree-check.txt over logs/all-results.jsonl (the
  bootstrap, edit-runs and rebase-r1 build records of the review, copied, plus build/): all 1198 TCSlib/audits
  modules rc 0 at the final-head source hash; 0 errors; 219 sorry warnings (unchanged).
  (The two files were also checked directly once before the commit; those runs are not recorded; the recorded
  runs are build/.)
decls2: statements/decls2-two-files.tsv (6f853adc -> head, 2 files): 0 rows. statements/decls2-whole-pr.tsv
  (2ea4df08d -> head, all changed .lean): 68 ADDED, 42 REMOVED, 2 MOVED, 0 CHANGED. touched-two-files.tsv: private
  ofFn_arrowCongr REMOVED; ofFn_block_eq_take_drop, ofFn_appendEquiv, ofFn_splitCoins_symm_cast proof-changed.
axioms: probe-sources/DlProbe/AxProbeGate20.lean (tools/mkcensus.py head side, owners OneWayLemmas and UniversalPadding,
  33 #print axioms: the 2 OneWay lemmas, 15 public UniversalPadding theorems, 16 endpoints), probe-runs/,
  logs/axioms-summary.txt. Probe files deleted from the worktree and the olean tree afterwards.
seals: probe-sources/DlProbe/CollectGate20.lean -> probe-runs/ collector log; tools/mkseals_ab.py with the archived
  gate10 harness (tools/archived-gate10-tools): seals/{A,B} at HEAD, base-seals/{A,B} at 6f853adc (old source over
  the same closure; records, manifests and .lean.txt sources), seal-runs/ (8 probes; results.jsonl, mods/*.log);
  tools/sealsum.py -> logs/seal-{head,base}-{A,B}.tsv, logs/seal-compare.txt.
controls: tools/mkctl_dl.py per file (controls/records-*, controls/out-*/ plans and sources), control-runs/,
  tools/ctlcheck2.py -> controls/controls-result-*.json, logs/ctlcheck-*.log (ALL_OK True in both).
lint/widths/sizes: logs/lint-{parent,head}.log (parent = git archive of 6f853adc), lint-diff.txt (empty),
  logs/widths-sizes.txt. Tool hashes: logs/tools-sha256.txt (tools/ holds copies of every tool used).
evidence zip: $SP/dl-review/gate20-r1-evidence.zip holds exactly the paths of SHA256SUMS (relative to gate20-r1/);
  SHA256SUMS itself sits beside it in gate20-r1/.

## ===== briefs/pass-shelat-ch5-8/gates/20-dl-consolidation/pack.md =====

# Gate 20 · Duplication consolidation DL-30–DL-34

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #298](https://github.com/Shilun-Allan-Li/tcslib/pull/298) at
  `6f853adc61d5d175ee83c69f6c07ab2da112cabc` (branch `land/pass-shelat-dl-consolidation`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` at base
  `2ea4df08d009a4bbdb8042795ff062d7f22db325`. That is the records tip after the #297 merge `758a1030`.
- **Issue base:** `b96ab3ccc1915497ea3138df499eec00b6581db0`, the merge of #293. Between that base and the PR base,
  the Lean changes are #294 (IND-CCA2 ⇔ NM-CCA2) and #297 (Theorem 174.8). The landing edits re-point both.
- **Commits:**
  - the worker's 4 commits (Claude job `dl-consolidation`): checkpoints 1–3, then R3/R4/Eager;
  - 5 maintainer landing edits: LE-split, LE-repoint, LE-review, LE-rule10 and LE-repoint-nmsim.
- **Scope:** a **refactor audit**.
  - The job promotes generic lemmas to shared homes, deletes the copies and re-points every use.
  - It is meant to change no audited statement and no mathematical content.
  - The brief is `fills/dl-consolidation/issued-r1/brief.md` on the records branch. Its items are P1–P4, S1–S3,
    H1, A1–A6, L1–L7, R1–R7 and O1–O2. The duplication ledger is `duplication-ledger.md`, rows DL-30 to DL-34 and
    DL-37.

## What changed

All paths are under `TCSlib/Cryptography/`. Across 51 Lean files, 48 are modified, 2 are added and 1 is deleted:
- added `Foundations/BitLists.lean`;
- added `Encryption/PublicKey/OracleSecurity/PaddedCPA.lean`;
- deleted `Encryption/PublicKey/BitwiseCPA/Eager.lean`.

**New shared homes**
- `Games/Probability` (`Games.ProbComp`): `expect_sample_equiv/_comm/_unique`, `expect_sub`, `expect_sample_update`,
  `abs_expect_sub_le`.
- `Games/Simulate`: `simulate_eq_of_abs` and the bounded form `simulate_eq_of_abs_bounded`.
- `Games/Hopping`: `expect_simulate_congr`, `prob_bad_le`, `expect_sample_mem_le`.
- `Games/BitCodec`:
  - the `castImpl` family;
  - `padFin_ofFn_zeroBits`, `padFin_nil`, `padFin_replicate_false`;
  - `decodeFin_nil_getD`.
- `Asymptotic/Adversary`, beside `padFin` and `blocks`:
  - `ofFn_padFin_of_length` (root);
  - `ofFn_cast`;
  - `ofFn_arrowCongr_finCongr`;
  - `FunFamily.ofFn_blocks`.
- `Asymptotic/EnsemblesLemmas`: A4's `EnsembleLemmas.ofFn_padFin_eq_padL`.
- Published readers:
  - `indCodec_eq_bitCodec` (public and private key);
  - `hybridPre_eq`;
  - R3's `expect_simulate_indImpl_cpa`;
  - R4's padded readers;
  - R5's general `chRun_toCompOn_transport_list`;
  - R6's round-input readers `InteractiveHandler.rU`…`rCnt` and `impl_of_ret`.
- `Foundations/BitLists`: the list and vector lemmas L1–L7.
- `ChallengeSim.expect_simulate_eager` (S3b; formerly `BitwiseSim`'s).

**The census of stored constants** (issue base → delivered head): 2112 → 2099.
- 101 removed, every one a listed copy or helper, with no aliases left behind.
- 88 added and 11 moved.
- The worker's name map is `namemap.txt` in its delivery (exchange `fc1082ca`, `inbox/fills/dl-consolidation/evidence/namemap.txt`). The
  census's own map is `statements/census-namemap.tsv` in `verification.zip`. The worker's map lacks two R4 rows,
  `BitwiseSim.padded_enc_runAt`/`_coins` → `PublicKeyScheme.*`; their types are identical by the census
  (review finding 6).

**The only type change modulo the name map** is R3: `expect_simulate_indImpl_cpa` goes from a private lemma to a
public one in cast form, as Rule 10 needs. Its uses are re-pointed.

**Landing edits**
- **LE-split** `406b8d57`: `section PaddedCPA` moves verbatim to `OracleSecurity/PaddedCPA.lean`, because with
  #294 `OracleSecurity.lean` would have been 1004 lines.
  - Sizes are now 723 and 332.
  - `TrapdoorCPA`, `BitwiseCPA` and the `Encryption/PublicKey` facade import it.
  - There is no import cycle.
- **LE-repoint** `06fab435`: #294's `Indistinguishability.lean`, `Decrypt.lean` and `Encrypt.lean` are re-pointed to
  the moved names.
- **LE-review** `82f8d1bc`: docstrings only.
- **LE-rule10** `510e9d75`: the proof of `padded_cpa_advantage_eq` now reads OracleSecurity through `padded_gen`,
  `padded_enc`, R1 and `ofFn_cast`. This was needed once OracleSecurity's definitions became foreign to the new
  file.
- **LE-repoint-nmsim** `6f853adc`: #297's nm-sim files are re-pointed (25 `ofFn_padFin_of_length` sites, among
  others).
  - The selective `open AdaptiveCPA (…)` lines are removed.
  - nm-sim's private `padFin_replicate_false` is deleted in favour of `Games.padFin_replicate_false`. This is the
    first payback of DL-37.
  - The statements of `castImpl_snmImpl` and `castImpl_indImpl_abs` keep the unqualified spelling `castImpl`,
    which resolves to `Games.castImpl` through `open TCSlib.Cryptography.Games`. Their text is byte-identical.

## Questions for the audit

**1. Statement freeze**
- Does any audited statement change, up to the name map?
- decls2 from the PR base to the head gives 68 ADDED, 42 REMOVED, 2 MOVED and **0 CHANGED**
  (`review.md`; `landing.zip:statements-r2/decls2-pr.tsv`).
- `padded_cpa` moves with an identical statement.
- Check the endpoints:
  - `prfFixedScheme_cpa`, `prfFixedScheme_cca1`, `not_prfFixedScheme_cca2`, `prfFixedScheme_not_cca2`;
  - `INDSecure.adaptive_cpa`;
  - `SingleBitSecure.bitwise_padded_cpa`, `exists_adaptive_cpa` and `padded_cpa`;
  - `exists_adaptiveCPA_of_rsa`/`_of_factoring`;
  - #294's `nmSecure_cca2_of_indSecure_cca2`, `indSecure_cca2_of_nmSecure_cca2` and `indSecure_cca2_iff_nmSecure_cca2`;
  - #297's `nmSecure_of_simNMSecure`, `simNMSecure_of_nmSecure_cpa` and `simNMSecure_cpa_iff_nmSecure_cpa`.

**2. Faithful promotion**
- Is each promoted lemma at least as general as every copy it replaces?
- Is each derived lemma (S1, A5, R5) really a corollary?
- Is any deleted copy still needed under another name?
- Was any copy that the brief or the worker's grep found left in place without a recorded reason?

**3. Rule 10** (no touched declaration reads another file's definition, including generated matchers and projections)
- Whole-file seals over the full closures: A 34/41 and B 30/41 at the head, against 33/40 and 28/40 at the base.
- No head failure is new: each one sits at the same declaration as at the base.
- `PaddedCPA` and `BitLists` pass both variants, and the 11 nm-sim files pass 22/22.
- Paired controls are ALL_OK, and the explicit-unfold scan finds 0 foreign definitions.
- The worker's table says `Games/Probability` passes. Under the archived harness it fails at the unchanged
  `dist_apply`, identically at base and head.
- Is LE-rule10 sufficient?
- Did any promotion move a definition's reader so that an existing proof now reads across files?

**4. Homes and API (policy §1, §3)**
- Is each lemma at its lowest legal home, with no import cycle?
- Names, formula docstrings, module docstrings and sketches.
- No `@[simp]` is added.
- The R6 readers are public with `*_input` readers but no `_eq`; lint check 8 accepts this (review finding 7).
- Are R7 (the length vectors, escalated and recommended closed as no-fold) and P2 (kept) correctly decided?

**5. Landing correctness**
- Is the LE-split verbatim?
- Do the re-points in #294's and #297's files change only names, `open` lines and widths?
- Are the two `castImpl` statement spellings really byte-identical?

## Also check

**Axioms**
- Every stored constant is standard, except the 4 Yao constants with base admissions; they are the same 4 as at
  the base.
- All 16 endpoints above print `[propext, Classical.choice, Quot.sound]` (`landing/axioms-head.log`).

**Admissions:** issued modules go 48 → 45. That is #294's 1 fill and nm-sim's 2. Nothing outside the issued order
changed (219 warnings in all).

**Lint:** FAIL 214 → 216 and WARN 103 → 103 against the PR base.
- The delta is +4 FAILs from the split: `OracleSecurity.lean` is linted as the facade of `OracleSecurity/` but cannot
  import `PaddedCPA` without a cycle, and `Encryption.lean` does not import the new grandchild.
- It is −2 FAILs from deleting `Eager`.
- The maintainer accepted this: a content file that shares a name with a directory is not a facade.

**Sizes and widths**
- Every changed file is under 1000 lines except `ElGamal` (1830, inherited; 1835 at the base).
- No changed file gains a line over 100 characters. The 160 such lines in 13 files are inherited, and
  `EfficiencyRep` lost one. `source-head.json` has the per-file counts.

**Duplication**
- DL-36 and DL-37 are open debt, with named payback after this landing. That is not a finding.
- What you can raise:
  - a copy this job should have folded and did not;
  - a fold that `review.md` § *Debt now foldable* misses.

## Evidence

- **`review.md`:** the maintainer's delivery review, ACCEPT WITH LANDING EDITS, followed by the rebase-r1 addendum.
- **`verification.zip`** (= `fills/dl-consolidation/final-r1/review-evidence.zip`): the review's raw evidence.
  - It covers:
    - integrity (`git am` reproduces the worker's commits);
    - the fresh 1219/1219 build;
    - the census and name map;
    - decls2;
    - axioms;
    - seals at base and head, with controls;
    - the unfold scan;
    - lint;
    - sizes.
  - `PROVENANCE.txt` describes it. The inner `SHA256SUMS` (2441 entries) covers the whole review directory,
    including raw seal sources left out for size.
- **`landing.zip`** (= `fills/dl-consolidation/final-r1/rebase-r1/rebase-evidence.zip`): the rebase onto #297 and
  LE-repoint-nmsim.
  - It holds the range-diff, the rebase check, the re-point counts, the 15-module rebuild and the final-tree check.
  - It also holds statements, axioms, the nm-sim seals and controls, the consolidation seal-closure check, the
    census and lint.
  - **`statements-r2/` supersedes `statements/decls2-nmsim.tsv`.** That file was written before the amend that
    kept the `castImpl` spellings.
- **`landing/`:** at the final head.
  - `root-order.txt` and `root-checks.jsonl`: the 15 rebuilt modules through root `TCSlib`, all rc 0, each with
    its `source_sha256`.
  - `final-tree-check.txt`: all 1198 TCSlib/`audits` modules end with rc 0 at the head's source hash.
  - `axioms-head.log`.
- **`worker-report.md`:** the worker's `REPORT.md`, at exchange `fc1082caa8455afab5342e9ba444955ade2994fd`.
- **`pr.diff.txt`:** `git diff` from the base to the head.
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 50 changed files, and the
  deleted file.
- **`sources.zip`:** the source closure at the head of every changed module (240 files).

## Findings delivery

Return `gate20-dl-consolidation-findings.md` as a Markdown file in this chat. If you have several evidence files,
return a ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, or a scope violation.
- **major:** a changed audited statement, a lost generality, a forbidden new read in a touched declaration, or
  necessary evidence that cannot be verified.
- **minor:** documentation or API defects.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

## ===== TCSlib/Cryptography/Asymptotic/OneWayLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.OneWayFunctions.Amplification
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the one-way function theorems

The machine-level and list-level infrastructure behind the fills of
`TCSlib.Cryptography.Asymptotic.OneWay` ([PS10, Theorems 35.1 and 35.2]): the file is
imported by `OneWay.lean`, so it cannot mention `FunFamily`; every statement is about strings,
`Fin`-indexed tuples (blocks through `finProdFinEquiv`), the concrete experiments of
`TCSlib.Cryptography.Foundations.Experiments` and the machine calculus of
`TCSlib.Complexity.Randomized`.

* **Blocks of a string.** A string of `q·ℓ` bits is `q` consecutive blocks of `ℓ` bits; block `i`
  of `x : Fin (q·ℓ) → Bool` is `fun j => x (finProdFinEquiv (i, j))` (the `blocks` bijection of
  `OneWay.lean` unfolds to this), and `ofFn_block_eq_take_drop` reads it off `List.ofFn x` by
  `drop`/`take`.
* **Planting** (`invProbOpt_prodFun_le_yaoTryOpt`): the `Option`-valued form of
  `OneWay.invProb_prodFun_le_yaoTry` — planting a challenge at a fixed position of a fresh tuple
  inverts `f` at least as often as the given inverter inverts the direct product.
* **Bridges** between the `List.find?` of `Complexity.polyTimeComputable_iterateFind` and the
  `foldr`/`findSome?` of `OneWay.yaoInverter` and `rejectionSample`.
* **Statistical closeness of products** over `Fin N` (`statClose_pi`): the `T + 1` rounds of
  rejection-sampled positions of Algorithm 38.5 are within `(T + 1)·δ` of uniform.
* **Sub-machines** of Algorithm 38.5 as `PolyTimeComputable` functions with clean
  specifications: the blockwise evaluator `exists_prodEval` (the honest evaluator of the direct
  product and of the fresh tuple `(f(x₁), …, f(x_m))`), the capped binary-to-unary converter
  `exists_unaryOf`, and the rejection sampler of the position `exists_posMachine`.

## Main definitions

* `TCSlib.Cryptography.OneWay.bitListToNat` — a bit string read as a number, most significant bit
  first (the list form of `bitsToNat`).
* `TCSlib.Cryptography.OneWay.padTrue` — pad or truncate a string to `ℓ` bits with `true`.

## Main results

* `TCSlib.Cryptography.OneWay.invProbOpt_prodFun_le_yaoTryOpt` — one-call planting, `Option` form.
* `TCSlib.Cryptography.OneWay.statClose_pi` — closeness of `Fin N`-indexed products.
* `TCSlib.Cryptography.OneWay.exists_prodEval`, `exists_unaryOf`, `exists_posMachine` — the
  sub-machines of [PS10, Algorithm 38.5].
* `TCSlib.Cryptography.OneWay.foldr_ite_eq_find?`, `findSome?_eq_bind_find?`,
  `find?_range_eq_map_find?_finRange` — loop bridges.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.4: Theorems 35.1, 35.2 and Algorithm 38.5.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1, Figure 2.2: the concrete amplification).
-/

namespace TCSlib.Cryptography.OneWay

open Complexity Turing Finset

/-! ### Blocks of a string -/

/-- Block `i` of `x : Fin (q * ℓ) → Bool` (positions `ℓ·i, …, ℓ·i + ℓ - 1`) is the `ℓ`-bit window
of `List.ofFn x` after `i·ℓ` bits.

**Proof sketch.** The block is `FunFamily.blocks q ℓ x i` (`FunFamily.blocks_apply`), whose word is
that window (`FunFamily.ofFn_blocks`). -/
theorem ofFn_block_eq_take_drop {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
    List.ofFn (fun j : Fin ℓ => x (finProdFinEquiv (i, j))) =
      ((List.ofFn x).drop (i * ℓ)).take ℓ := by
  have hblk : (fun j : Fin ℓ => x (finProdFinEquiv (i, j))) = FunFamily.blocks q ℓ x i :=
    funext fun j => (FunFamily.blocks_apply q ℓ x i j).symm
  rw [hblk, FunFamily.ofFn_blocks]

/-- The window of `ℓ` bits after `i·ℓ` bits of `List.ofFn x` has exactly `ℓ` bits. -/
theorem length_take_drop_block {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
    (((List.ofFn x).drop (i * ℓ)).take ℓ).length = ℓ := by
  rw [← ofFn_block_eq_take_drop, List.length_ofFn]

/-- The concatenation of two chunks indexed by `Fin 2`. -/
theorem flatten_ofFn_two (g : Fin 2 → List Bool) : (List.ofFn g).flatten = g 0 ++ g 1 := by
  simp [List.ofFn_succ]

/-- Reading the first `m` coordinates of a tuple is taking the first `m` bits of its encoding. -/
theorem ofFn_castLE_eq_take {m k : ℕ} (h : m ≤ k) (a : Fin k → Bool) :
    List.ofFn (fun j : Fin m => a (Fin.castLE h j)) = (List.ofFn a).take m := by
  refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
  simp

/-- Pad with `true` or truncate a string to exactly `ℓ` bits (the convention of the block
extraction of Algorithm 38.5: a malformed answer of the given inverter is padded). -/
def padTrue (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i true

/-- The encoding of `padTrue ℓ w` is `w` padded with `1^ℓ` and cut to `ℓ` bits. -/
theorem ofFn_padTrue (ℓ : ℕ) (w : List Bool) :
    List.ofFn (padTrue ℓ w) = (w ++ List.replicate ℓ true).take ℓ := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, padTrue, List.getElem_take]
  rw [List.getD_eq_getElem?_getD]
  by_cases hj : j < w.length
  · rw [List.getElem_append_left hj, List.getElem?_eq_getElem hj, Option.getD_some]
  · rw [List.getElem_append_right (not_lt.1 hj), List.getElem_replicate,
      List.getElem?_eq_none (not_lt.1 hj), Option.getD_none]

/-- Padding the encoding of an `ℓ`-bit string returns it. -/
theorem padTrue_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padTrue ℓ (List.ofFn x) = x := by
  funext i
  simp [padTrue]

/-- Padding the tail of the encoding of a `q·ℓ`-bit tuple after `i·ℓ` bits gives block `i`. -/
theorem padTrue_drop_ofFn {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
    padTrue ℓ ((List.ofFn x).drop (i * ℓ)) = fun j => x (finProdFinEquiv (i, j)) := by
  apply List.ofFn_injective
  rw [ofFn_padTrue, ofFn_block_eq_take_drop]
  have h := length_take_drop_block x i
  rw [List.length_take] at h
  rw [List.take_append_of_le_length (by omega)]

/-- A bit string read as a number, most significant bit first: the list form of `bitsToNat`
(`bitsToNat b = bitListToNat (List.ofFn b)` by definition). -/
def bitListToNat (l : List Bool) : ℕ := l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0

/-- `bitsToNat` is `bitListToNat` of the encoding. -/
theorem bitsToNat_eq_bitListToNat {k : ℕ} (b : Fin k → Bool) : bitsToNat b = bitListToNat (List.ofFn b) :=
  bitsToNat_def b

/-- Reading one more bit: `bitListToNat (l ++ [c]) = 2 · bitListToNat l + c`. -/
theorem bitListToNat_append_singleton (l : List Bool) (c : Bool) :
    bitListToNat (l ++ [c]) = 2 * bitListToNat l + (if c then 1 else 0) := by
  simp [bitListToNat, List.foldl_append]

/-- Prefix values are monotone: the number read from a prefix is at most the number read from
the whole string.

**Proof sketch.** Induction on the string: reading the remaining bits after a prefix of value
`a` gives `a · 2^{rest} + value(rest)`, so a longer suffix can only increase the value
(`Nat.pow_le_pow_right`). -/
theorem bitListToNat_take_le (l : List Bool) : ∀ i, bitListToNat (l.take i) ≤ bitListToNat l := by
  intro i
  induction l generalizing i with
  | nil => simp [bitListToNat]
  | cons c l ih =>
    cases i with
    | zero => simp [bitListToNat]
    | succ i =>
      rw [List.take_succ_cons]
      have key : ∀ (m : List Bool) (a : ℕ),
          m.foldl (fun a c => 2 * a + (if c then 1 else 0)) a =
            a * 2 ^ m.length + m.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := by
        intro m
        induction m with
        | nil => simp
        | cons d m ihm =>
          intro a
          rw [List.foldl_cons, List.foldl_cons, ihm, ihm (2 * 0 + _), List.length_cons, pow_succ]
          ring
      simp only [bitListToNat, List.foldl_cons] at ih ⊢
      rw [key (l.take i), key l]
      have h1 := ih i
      have h2 : (l.take i).length ≤ l.length := List.length_take_le' _ _
      have h3 : 2 ^ (l.take i).length ≤ 2 ^ l.length := Nat.pow_le_pow_right (by norm_num) h2
      have h4 : 0 ≤ (if c then 1 else 0 : ℕ) := Nat.zero_le _
      nlinarith [Nat.mul_le_mul_left (2 * 0 + (if c then 1 else 0)) h3]

/-! ### Planting, `Option` form -/

/-- **One-call planting, `Option` form** (the `invProbOpt` variant of
`OneWay.invProb_prodFun_le_yaoTry`, anticipated by the proof sketch of [PS10, Theorem 35.2]):
for a possibly failing inverter `B` of the direct product and a fixed position `i`, the
inverter that samples a fresh tuple, plants the challenge at position `i`, calls `B` and returns
the `i`-th component of its answer inverts `f` at least as often as `B` inverts `prodFun f q`.

**Proof sketch.** As `invProb_prodFun_le_yaoTry`: the planted tuple is uniform
(`OneWay.uprob_update`, `prodFun_update`), and an inverse of the whole tuple inverts every
coordinate (`uprob_mono`). -/
theorem invProbOpt_prodFun_le_yaoTryOpt {α β ρ : Type*} [Fintype α] [Nonempty α] [DecidableEq β]
    [Fintype ρ] {q : ℕ} (f : α → β) (B : (Fin q → β) → ρ → Option (Fin q → α)) (i : Fin q) :
    invProbOpt (prodFun f q) B ≤
      invProbOpt f fun y (c : (Fin q → α) × ρ) =>
        (B (Function.update (prodFun f q c.1) i y) c.2).map fun xs => xs i := by
  simp only [invProbOpt_def]
  have h := uprob_update (α := α) (ρ := ρ) i fun xs r =>
    ∃ x', (B (prodFun f q xs) r).map (fun xs => xs i) = some x' ∧ f x' = f (xs i)
  simp only [prodFun_update, Function.update_self] at h
  refine le_trans ?_ (le_of_eq h.symm)
  apply uprob_mono
  rintro ⟨xs, r⟩ ⟨xs', hxs', hf⟩
  exact ⟨xs' i, by simp [hxs'], by simpa only [prodFun_apply] using congrFun hf i⟩

/-! ### Loop bridges -/

/-- The `foldr` of `OneWay.yaoInverter` returns the value at the first element satisfying the
test, or the default (`Option.elim` of the `List.find?`). -/
theorem foldr_ite_eq_find? {ι γ : Type*} (P : ι → Prop) [DecidablePred P] (v : ι → γ) (d : γ) :
    ∀ l : List ι, l.foldr (fun t acc => if P t then v t else acc) d =
      (l.find? (fun t => decide (P t))).elim d v := by
  intro l
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.foldr_cons, List.find?_cons, ih]
    by_cases h : P t <;> simp [h]

/-- `findSome?` is `find?` of the successful indices followed by the function. -/
theorem findSome?_eq_bind_find? {ι γ : Type*} (f : ι → Option γ) :
    ∀ l : List ι, l.findSome? f = (l.find? fun t => (f t).isSome).bind f := by
  intro l
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.findSome?_cons, List.find?_cons]
    cases hf : f t <;> simp [hf, ih]

/-- A search over `List.range N` with a test that agrees with `p` below `n ≤ N` and fails from
`n` on is the search over `List.finRange n`. -/
theorem find?_range_eq_map_find?_finRange {n N : ℕ} (hN : n ≤ N) (p : Fin n → Bool) (p' : ℕ → Bool)
    (hp : ∀ (t : ℕ) (h : t < n), p' t = p ⟨t, h⟩) (hp' : ∀ t, n ≤ t → p' t = false) :
    (List.range N).find? p' = ((List.finRange n).find? p).map Fin.val := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction d with
  | zero =>
    rw [Nat.add_zero, ← List.map_coe_finRange, List.find?_map]
    congr 2
    funext t
    exact hp t.1 t.2
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.find?_append, ih (Nat.le_add_right n d)]
    have : [n + d].find? p' = none := by simp [hp' (n + d) (Nat.le_add_right n d)]
    rw [this, Option.or_none]

/-! ### The direct product's evaluator -/

/-- The concatenation of `R` chunks of which only the first `Q ≤ R` are nonempty is the
concatenation of the first `Q`. -/
theorem flatMap_range_ite_eq_flatten_ofFn (E : ℕ → List Bool) {Q R : ℕ} (h : Q ≤ R) :
    (List.range R).flatMap (fun i => if Q ≤ i then [] else E i) =
      (List.ofFn fun j : Fin Q => E j).flatten := by
  have base : (List.range Q).flatMap (fun i => if Q ≤ i then [] else E i) =
      (List.ofFn fun j : Fin Q => E j).flatten := by
    rw [List.ofFn_eq_map, List.flatMap_def, ← List.map_coe_finRange, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    rw [if_neg (not_le.2 t.2)]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simpa using base
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.flatMap_append]
    have : [Q + d].flatMap (fun i => if Q ≤ i then [] else E i) = [] := by
      simp [Nat.le_add_right Q d]
    rw [this, List.append_nil]
    exact ih (Nat.le_add_right Q d)

/-! ### Statistical closeness of `Fin N`-indexed products -/

/-- **Closeness of products over `Fin N`:** if `X` is `δ`-close to `Y` then `N` independent
copies are `N·δ`-close (the `T + 1` rounds of rejection-sampled positions of
[PS10, Algorithm 38.5] are within `(T + 1)·δ` of uniform).

**Proof sketch.** Induction on `N`. For `N = 0` both samplers are constant. For `N + 1`,
split off the first coordinate with `Fin.consEquiv`: the pair sampler is `StatClose.prod` of
one copy and `N` copies (`δ + N·δ`), post-processed by `Fin.cons` (`StatClose.map`) and
re-indexed by the bijection on both sides (`StatClose.comp_equiv_left/right`);
`Fin.cons (c 0) (Fin.tail c) = c` identifies the samplers. -/
theorem statClose_pi {σ τ γ : Type*} [Fintype σ] [Fintype τ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (N : ℕ) :
    StatClose (fun c : Fin N → σ => fun t => X (c t)) (fun c : Fin N → τ => fun t => Y (c t))
      (N * δ) := by
  induction N with
  | zero =>
    refine (statClose_iff _ _ _).2 fun T => ?_
    have hX : ∀ c : Fin 0 → σ, (fun t => X (c t)) = (fun t : Fin 0 => t.elim0) :=
      fun c => funext fun t => t.elim0
    have hY : ∀ c : Fin 0 → τ, (fun t => Y (c t)) = (fun t : Fin 0 => t.elim0) :=
      fun c => funext fun t => t.elim0
    simp only [hX, hY, Nat.cast_zero, zero_mul]
    by_cases hT : T (fun t : Fin 0 => t.elim0)
    · simp [hT, uprob_true]
    · simp [hT, uprob_false]
  | succ N ih =>
    have hp := ((h.prod ih).map (fun p : γ × (Fin N → γ) => (Fin.cons p.1 p.2 : Fin (N + 1) → γ)))
    have hp2 := (hp.comp_equiv_left (Fin.consEquiv (fun _ => σ)).symm).comp_equiv_right
      (Fin.consEquiv (fun _ => τ)).symm
    have keyX : ∀ c : Fin (N + 1) → σ,
        (Fin.cons (X (c 0)) (fun t => X (Fin.tail c t)) : Fin (N + 1) → γ) = fun t => X (c t) := by
      intro c
      funext t
      refine Fin.cases ?_ (fun t => ?_) t
      · simp
      · simp [Fin.tail_def]
    have keyY : ∀ c : Fin (N + 1) → τ,
        (Fin.cons (Y (c 0)) (fun t => Y (Fin.tail c t)) : Fin (N + 1) → γ) = fun t => Y (c t) := by
      intro c
      funext t
      refine Fin.cases ?_ (fun t => ?_) t
      · simp
      · simp [Fin.tail_def]
    have hδ : ((N + 1 : ℕ) : ℝ) * δ = δ + N * δ := by push_cast; ring
    rw [hδ]
    convert hp2 using 1
    · funext c
      simp only [Fin.consEquiv_symm_apply]
      exact (keyX c).symm
    · funext c
      simp only [Fin.consEquiv_symm_apply]
      exact (keyY c).symm

/-! ### Unary multiplication at the FP level -/

/-- The FP form of the unary-multiplication machine: `⟨u, v⟩ ↦ 1^{|u|·|v|}` (with the total
projections, so `[]` on malformed words). -/
theorem polyTimeComputable_unaryMulPair :
    PolyTimeComputable fun z => List.replicate ((pairFstD z).length * (pairSndD z).length) true := by
  have h := polyTimeComputable_unary.comp
    (BinArith.polyTimeComputable_mulU.comp
      (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD))
  refine h.congr fun z => ?_
  simp only [Function.comp_apply, BinArith.length_mulU]

/-! ### The blockwise evaluator -/

namespace ProdEval

/-- The parameter slot `u` of the state word `⟨⟨u, cnt⟩, rest⟩`. -/
def u (w : List Bool) : List Bool := pairFstD (pairFstD w)

/-- The unary round counter `cnt` of the state word `⟨⟨u, cnt⟩, rest⟩`. -/
def cnt (w : List Bool) : List Bool := pairSndD (pairFstD w)

/-- The unread input `rest` of the state word `⟨⟨u, cnt⟩, rest⟩`. -/
def rest (w : List Bool) : List Bool := pairSndD w

/-- The initial state word `⟨⟨u, []⟩, x⟩` of the input `⟨u, x⟩`. -/
def start (z : List Bool) : List Bool := pairEncode (pairEncode (pairFstD z) []) (pairSndD z)

/-- One round: add a token to the counter and drop one block of `inLen(|u|)` bits. -/
def step (inLen : PolyExpr) (w : List Bool) : List Bool :=
  pairEncode (pairEncode (u w) (true :: cnt w)) ((rest w).drop (inLen.eval (u w).length))

/-- The emission of a round: `F ⟨u, next block⟩` while fewer than `q(|u|)` rounds have run,
`[]` afterwards. -/
def emit (F : List Bool → List Bool) (inLen q : PolyExpr) (w : List Bool) : List Bool :=
  if q.eval (u w).length ≤ (cnt w).length then []
  else F (pairEncode (u w) ((rest w).take (inLen.eval (u w).length)))

/-- The parameter slot is polynomial-time. -/
theorem u_poly : PolyTimeComputable u := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- The counter is polynomial-time. -/
theorem cnt_poly : PolyTimeComputable cnt :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD

/-- The unread input is polynomial-time. -/
theorem rest_poly : PolyTimeComputable rest := polyTimeComputable_pairSndD

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_const [])).pairEncode
    polyTimeComputable_pairSndD

/-- Dropping the current block is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly`
on `⟨u, rest⟩`). -/
theorem drop_poly (inLen : PolyExpr) :
    PolyTimeComputable fun w => (rest w).drop (inLen.eval (u w).length) := by
  convert (polyTimeComputable_pairDropPoly inLen).comp (u_poly.pairEncode rest_poly) using 1
  funext w
  simp

/-- Reading the current block is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly`
on `⟨u, rest⟩`). -/
theorem take_poly (inLen : PolyExpr) :
    PolyTimeComputable fun w => (rest w).take (inLen.eval (u w).length) := by
  convert (polyTimeComputable_pairTakePoly inLen).comp (u_poly.pairEncode rest_poly) using 1
  funext w
  simp

/-- The step is polynomial-time. -/
theorem step_poly (inLen : PolyExpr) : PolyTimeComputable (step inLen) :=
  (u_poly.pairEncode ((StateLoop.cons_poly true).comp cnt_poly)).pairEncode (drop_poly inLen)

/-- The emission is polynomial-time (`StateLoop.lenLe_comp` against `1^{q(|u|)}`,
`Complexity.polyTimeComputable_ite`). -/
theorem emit_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) (inLen q : PolyExpr) :
    PolyTimeComputable (emit F inLen q) := by
  have htest : PolyTimeComputable fun w => [decide (q.eval (u w).length ≤ (cnt w).length)] := by
    convert StateLoop.lenLe_comp cnt_poly (StateLoop.unaryPoly_comp q u_poly) using 1
    funext w
    simp
  convert polyTimeComputable_ite htest (polyTimeComputable_const [])
    (hF.comp (u_poly.pairEncode (take_poly inLen))) using 1
  funext w
  by_cases h : q.eval (u w).length ≤ (cnt w).length <;> simp [emit, h]

/-- The orbit of an arbitrary word after `i + 1` rounds: the parameter is retained, the counter
has grown by `i + 1` tokens and `(i + 1)` blocks have been dropped. -/
theorem iterate_step_succ (inLen : PolyExpr) (w : List Bool) (i : ℕ) :
    (step inLen)^[i + 1] w =
      pairEncode (pairEncode (u w) (List.replicate (i + 1) true ++ cnt w))
        ((rest w).drop ((i + 1) * inLen.eval (u w).length)) := by
  induction i with
  | zero => simp [step]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, u, cnt, rest, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
    congr 2
    ring

/-- The orbit of an arbitrary word `w` stays within `4|w| + 2i + 6` after `i` rounds. -/
theorem length_iterate_step_le (inLen : PolyExpr) (w : List Bool) (i : ℕ) :
    ((step inLen)^[i] w).length ≤ 4 * w.length + 2 * i + 6 := by
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [iterate_step_succ, length_pairEncode, length_pairEncode, List.length_append,
      List.length_replicate]
    have h1 := length_pair_components_le w
    have h2 := length_pair_components_le (pairFstD w)
    have h3 : ((rest w).drop ((i + 1) * inLen.eval (u w).length)).length =
        (rest w).length - (i + 1) * inLen.eval (u w).length := List.length_drop
    simp only [u, cnt, rest] at h2 h3 ⊢
    omega

/-- The orbit on a genuine input `⟨⟨1^n, []⟩, x⟩`: `⟨⟨1^n, 1^i⟩, x.drop (i·inLen(n))⟩`. -/
theorem iterate_step_start (inLen : PolyExpr) (n : ℕ) (x : List Bool) (i : ℕ) :
    (step inLen)^[i] (start (pairEncode (List.replicate n true) x)) =
      pairEncode (pairEncode (List.replicate n true) (List.replicate i true))
        (x.drop (i * inLen.eval n)) := by
  cases i with
  | zero => simp [start]
  | succ i =>
    rw [iterate_step_succ]
    simp [start, u, cnt, rest]

end ProdEval

/-- **The blockwise evaluator** (the honest evaluator of the direct product of
[PS10, Theorem 35.1], and the evaluation of the fresh tuple of Algorithm 38.5): from a
polynomial-time `F` and syntactic lengths `inLen`, `q`, a polynomial-time `F'` with
`F' ⟨1^n, x⟩ = F ⟨1^n, x₀⟩ ++ ⋯ ++ F ⟨1^n, x_{q(n)-1}⟩` on every `q(n)·inLen(n)`-bit `x`
(`x_i` its `i`-th block).

**Proof sketch.** `Complexity.polyTimeComputable_iterateEmit` with `R := q` on the state word
`⟨⟨1^n, cnt⟩, rest⟩` (`ProdEval`): each round emits `F ⟨1^n, rest.take (inLen n)⟩` while the
unary counter is shorter than `1^{q(n)}` and `[]` afterwards, then drops `inLen n` bits and adds
a token (`ProdEval.iterate_step_start`); the orbit of every word is bounded by
`4|w| + 2q(|w|) + 6` (`ProdEval.length_iterate_step_le`). `q` is evaluated at the length of the
state word `≥ n`, so at least `q(n)` rounds emit (`PolyExpr.eval_mono`); the concatenation
of the first `q(n)` emissions is the target by `flatMap_range_ite_eq_flatten_ofFn` and
`ofFn_block_eq_take_drop`. -/
theorem exists_prodEval {F : List Bool → List Bool} (hF : PolyTimeComputable F)
    (inLen q : PolyExpr) :
    ∃ F' : List Bool → List Bool, PolyTimeComputable F' ∧
      ∀ (n : ℕ) (x : Fin (q.eval n * inLen.eval n) → Bool),
        F' (pairEncode (List.replicate n true) (List.ofFn x)) =
          (List.ofFn fun i : Fin (q.eval n) =>
            F (pairEncode (List.replicate n true)
              (List.ofFn fun j : Fin (inLen.eval n) => x (finProdFinEquiv (i, j))))).flatten := by
  have horbit : ∀ (w : List Bool) (i : ℕ), i ≤ q.eval w.length →
      ((ProdEval.step inLen)^[i] w).length ≤
        (PolyExpr.add (.mul (.const 4) .var) (.add (.mul (.const 2) q) (.const 6))).eval w.length := by
    intro w i hi
    have := ProdEval.length_iterate_step_le inLen w i
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  have hloop := polyTimeComputable_iterateEmit (ProdEval.step_poly inLen)
    (ProdEval.emit_poly hF inLen q) q _ horbit
  refine ⟨_, hloop.comp ProdEval.start_poly, fun n x => ?_⟩
  simp only [Function.comp_apply]
  have hlen : n ≤ (ProdEval.start (pairEncode (List.replicate n true) (List.ofFn x))).length := by
    simp only [ProdEval.start, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_replicate]
    omega
  have hQle : q.eval n ≤
      q.eval (ProdEval.start (pairEncode (List.replicate n true) (List.ofFn x))).length + 1 :=
    (q.eval_mono hlen).trans (Nat.le_succ _)
  have hemit : ∀ i, ProdEval.emit F inLen q
      ((ProdEval.step inLen)^[i] (ProdEval.start (pairEncode (List.replicate n true) (List.ofFn x)))) =
      if q.eval n ≤ i then []
      else F (pairEncode (List.replicate n true)
        (((List.ofFn x).drop (i * inLen.eval n)).take (inLen.eval n))) := by
    intro i
    rw [ProdEval.iterate_step_start]
    simp [ProdEval.emit, ProdEval.u, ProdEval.cnt, ProdEval.rest]
  simp only [hemit]
  rw [flatMap_range_ite_eq_flatten_ofFn _ hQle]
  congr 2
  funext i
  rw [ofFn_block_eq_take_drop]

/-! ### The capped binary-to-unary converter -/

namespace UnaryOf

/-- The pad `1^L` of the state word `⟨pad, ⟨rest, acc⟩⟩`: the cap on the accumulator. -/
def pad (w : List Bool) : List Bool := pairFstD w

/-- The unread bits of the state word `⟨pad, ⟨rest, acc⟩⟩`. -/
def rest (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The unary accumulator of the state word `⟨pad, ⟨rest, acc⟩⟩`. -/
def acc (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The accumulator doubled, plus the next bit: `1^{2a + bit}`. -/
def dbl (w : List Bool) : List Bool :=
  acc w ++ acc w ++ (if (rest w).headD false then [true] else [])

/-- The doubled accumulator, capped at the pad (so that the orbit of every word is bounded). -/
def capped (w : List Bool) : List Bool :=
  if (dbl w).length ≤ (pad w).length then dbl w else pad w

/-- One round: read one bit if any remain, else stay. -/
def step (w : List Bool) : List Bool :=
  if rest w = [] then w else pairEncode (pad w) (pairEncode (rest w).tail (capped w))

/-- The initial state `⟨pad, ⟨b, []⟩⟩` of the input `⟨pad, b⟩`. -/
def start (z : List Bool) : List Bool := pairEncode (pairFstD z) (pairEncode (pairSndD z) [])

/-- The pad is polynomial-time. -/
theorem pad_poly : PolyTimeComputable pad := polyTimeComputable_pairFstD

/-- The unread bits are polynomial-time. -/
theorem rest_poly : PolyTimeComputable rest :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The accumulator is polynomial-time. -/
theorem acc_poly : PolyTimeComputable acc :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- Doubling is polynomial-time. -/
theorem dbl_poly : PolyTimeComputable dbl := by
  have hbit : PolyTimeComputable fun w => [(rest w).headD false] :=
    polyTimeComputable_headD.comp rest_poly
  exact (acc_poly.append acc_poly).append
    (polyTimeComputable_ite hbit (polyTimeComputable_const [true]) (polyTimeComputable_const []))

/-- Capping is polynomial-time. -/
theorem capped_poly : PolyTimeComputable capped := by
  convert polyTimeComputable_ite (StateLoop.lenLe_comp pad_poly dbl_poly) dbl_poly pad_poly using 1
  funext w
  simp [capped]

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step := by
  convert polyTimeComputable_ite (polyTimeComputable_isNil.comp rest_poly) polyTimeComputable_id
    (pad_poly.pairEncode
        (((polyTimeComputable_tail.congr fun _ => List.drop_one).comp rest_poly).pairEncode
            capped_poly)) using 1
  funext w
  simp [step]

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))

/-- The capped accumulator never exceeds the pad. -/
theorem length_capped_le (w : List Bool) : (capped w).length ≤ (pad w).length := by
  unfold capped
  split_ifs with h
  · exact h
  · exact le_rfl

/-- The unread bits of any word are no longer than the word. -/
theorem length_rest_le (w : List Bool) : (rest w).length ≤ w.length := by
  have h1 := length_pairFstD_le (pairSndD w)
  have h2 := length_pair_components_le w
  unfold rest
  omega

/-- The orbit invariant on arbitrary words: the orbit point is the start word or a state word
`⟨pad w, ⟨r, a⟩⟩` with `|r| ≤ |w|` and `|a| ≤ |pad w|`. -/
def Inv (w w' : List Bool) : Prop :=
  w' = w ∨ ∃ r a : List Bool,
    w' = pairEncode (pad w) (pairEncode r a) ∧ r.length ≤ w.length ∧ a.length ≤ (pad w).length

/-- The invariant is preserved by the step. -/
theorem inv_step (w w' : List Bool) (h : Inv w w') : Inv w (step w') := by
  rcases h with rfl | ⟨r, a, rfl, hr, ha⟩
  · unfold step
    split_ifs with h0
    · exact Or.inl rfl
    · refine Or.inr ⟨(rest w').tail, capped w', rfl, ?_, length_capped_le w'⟩
      have := List.length_tail (l := rest w')
      have := length_rest_le w'
      omega
  · have hpad : pad (pairEncode (pad w) (pairEncode r a)) = pad w := by simp [pad]
    have hrest : rest (pairEncode (pad w) (pairEncode r a)) = r := by simp [rest]
    unfold step
    split_ifs with h0
    · exact Or.inr ⟨r, a, rfl, hr, ha⟩
    · refine Or.inr ⟨r.tail, capped (pairEncode (pad w) (pairEncode r a)), ?_, ?_, ?_⟩
      · rw [hpad, hrest]
      · have := List.length_tail (l := r)
        omega
      · have := length_capped_le (pairEncode (pad w) (pairEncode r a))
        rwa [hpad] at this

/-- A word satisfying the invariant has length at most `5|w| + 4`. -/
theorem length_le_of_inv {w w' : List Bool} (h : Inv w w') : w'.length ≤ 5 * w.length + 4 := by
  rcases h with rfl | ⟨r, a, rfl, hr, ha⟩
  · omega
  · have := length_pairFstD_le w
    simp only [length_pairEncode, pad] at *
    omega

/-- The whole orbit satisfies the invariant. -/
theorem inv_iterate (w : List Bool) (i : ℕ) : Inv w (step^[i] w) := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step w _ ih

/-- The orbit of every word stays within `5|w| + 4`. -/
theorem length_iterate_le (w : List Bool) (i : ℕ) : (step^[i] w).length ≤ 5 * w.length + 4 :=
  length_le_of_inv (inv_iterate w i)

/-- The orbit on a genuine input `⟨p, b⟩` with `bitListToNat b ≤ |p|`: after `i` rounds the state
is `⟨p, ⟨b.drop i, 1^{bitListToNat (b.take i)}⟩⟩`.

**Proof sketch.** Induction on `i`. While bits remain (`List.drop_eq_getElem_cons`), the step
doubles the accumulator and adds the bit `b[i]`, giving `1^{bitListToNat (b.take (i + 1))}`
(`List.take_append_getElem`, `bitListToNat_append_singleton`); the cap never fires because
`bitListToNat (b.take (i + 1)) ≤ bitListToNat b ≤ |p|` (`bitListToNat_take_le`). Once the bits are
exhausted the step is the identity and `b.take (i + 1) = b.take i`. -/
theorem iterate_start (p b : List Bool) (hb : bitListToNat b ≤ p.length) (i : ℕ) :
    step^[i] (start (pairEncode p b)) =
      pairEncode p (pairEncode (b.drop i) (List.replicate (bitListToNat (b.take i)) true)) := by
  induction i with
  | zero => simp [start, bitListToNat]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hi : i < b.length
    · have hdrop := List.drop_eq_getElem_cons hi
      have hdbl : dbl (pairEncode p (pairEncode (b.drop i)
          (List.replicate (bitListToNat (b.take i)) true))) =
          List.replicate (bitListToNat (b.take (i + 1))) true := by
        simp only [dbl, acc, rest, pairFstD_pairEncode, pairSndD_pairEncode, hdrop, List.headD_cons]
        rw [← List.take_append_getElem hi, bitListToNat_append_singleton, two_mul, List.replicate_add,
          List.replicate_add]
        cases hbi : b[i] <;> simp
      have hcap : capped (pairEncode p (pairEncode (b.drop i)
          (List.replicate (bitListToNat (b.take i)) true))) =
          List.replicate (bitListToNat (b.take (i + 1))) true := by
        unfold capped
        rw [hdbl, if_pos]
        rw [List.length_replicate]
        simp only [pad, pairFstD_pairEncode]
        exact (bitListToNat_take_le b (i + 1)).trans hb
      have hne : rest (pairEncode p (pairEncode (b.drop i)
          (List.replicate (bitListToNat (b.take i)) true))) ≠ [] := by
        simp only [rest, pairFstD_pairEncode, pairSndD_pairEncode, hdrop]
        exact List.cons_ne_nil _ _
      unfold step
      rw [if_neg hne, hcap]
      simp only [pad, rest, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop]
    · have hle : b.length ≤ i := not_lt.1 hi
      have h1 : b.drop i = [] := List.drop_eq_nil_of_le hle
      have h2 : b.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
      have h3 : b.take (i + 1) = b.take i := by
        rw [List.take_of_length_le hle, List.take_of_length_le (by omega)]
      rw [h2, h3]
      unfold step
      rw [if_pos (by simp [rest, h1]), h1]

end UnaryOf

/-- **The capped binary-to-unary converter**: a polynomial-time `U` with
`U ⟨p, b⟩ = 1^{bitListToNat b}` whenever `bitListToNat b ≤ |p|` (the pad `p` bounds the output; the
rejection sampler of Algorithm 38.5 reads each `k`-bit trial as a number below `2^k ≤ 2m`).

**Proof sketch.** `Complexity.polyTimeComputable_iterate` with `R := var` on the state word
`⟨p, ⟨rest, acc⟩⟩` (`UnaryOf`): each round doubles the unary accumulator and adds the next
bit, capped at the pad so that the orbit of every word stays within `5|w| + 4`
(`UnaryOf.length_iterate_le`); on a genuine input the cap never fires
(`UnaryOf.iterate_start`), and after `|b|` rounds the state is `⟨p, ⟨[], 1^{bitListToNat b}⟩⟩`. -/
theorem exists_unaryOf : ∃ U : List Bool → List Bool, PolyTimeComputable U ∧
    ∀ p b : List Bool, bitListToNat b ≤ p.length → U (pairEncode p b) = List.replicate (bitListToNat b) true := by
  have horbit : ∀ (w : List Bool) (i : ℕ), i ≤ PolyExpr.var.eval w.length →
      (UnaryOf.step^[i] w).length ≤ (PolyExpr.add (.mul (.const 5) .var) (.const 4)).eval w.length := by
    intro w i _
    simpa using UnaryOf.length_iterate_le w i
  have hiter := polyTimeComputable_iterate UnaryOf.step_poly .var _ horbit
  refine ⟨_, UnaryOf.acc_poly.comp (hiter.comp UnaryOf.start_poly), fun p b hb => ?_⟩
  simp only [Function.comp_apply, PolyExpr.eval_var]
  rw [UnaryOf.iterate_start p b hb]
  have hlen : b.length ≤ (UnaryOf.start (pairEncode p b)).length := by
    simp only [UnaryOf.start, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_nil]
    omega
  rw [List.drop_eq_nil_of_le hlen, List.take_of_length_le hlen]
  simp [UnaryOf.acc]

/-! ### The rejection sampler of the position -/

namespace PosLoop

/-- The trial length `1^k` of the state word `⟨⟨1^k, 1^m⟩, rest⟩`. -/
def ukk (v : List Bool) : List Bool := pairFstD (pairFstD v)

/-- The range `1^m` of the state word `⟨⟨1^k, 1^m⟩, rest⟩`. -/
def uM (v : List Bool) : List Bool := pairSndD (pairFstD v)

/-- The unread trials of the state word `⟨⟨1^k, 1^m⟩, rest⟩`. -/
def rest (v : List Bool) : List Bool := pairSndD v

/-- One round: drop one trial of `k` bits. -/
def step (v : List Bool) : List Bool := pairEncode (pairFstD v) ((rest v).drop (ukk v).length)

/-- The current trial: the next `k` bits. -/
def trial (v : List Bool) : List Bool := (rest v).take (ukk v).length

/-- The current trial as a unary number, through the converter `U` with pad `1^{2m}`. -/
def unum (U : List Bool → List Bool) (v : List Bool) : List Bool :=
  U (pairEncode (uM v ++ uM v) (trial v))

/-- The acceptance test: a full trial remains and its value is below `m`. -/
def acc (U : List Bool → List Bool) (v : List Bool) : Bool :=
  decide ((ukk v).length ≤ (rest v).length) && !decide ((uM v).length ≤ (unum U v).length)

/-- The trial length is polynomial-time. -/
theorem ukk_poly : PolyTimeComputable ukk := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- The range is polynomial-time. -/
theorem uM_poly : PolyTimeComputable uM := polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD

/-- The unread trials are polynomial-time. -/
theorem rest_poly : PolyTimeComputable rest := polyTimeComputable_pairSndD

/-- The step is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly` at `var`). -/
theorem step_poly : PolyTimeComputable step := by
  convert polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_pairDropPoly .var).comp (ukk_poly.pairEncode rest_poly)) using 1
  funext v
  simp [step]

/-- The current trial is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly` at `var`). -/
theorem trial_poly : PolyTimeComputable trial := by
  convert (polyTimeComputable_pairTakePoly .var).comp (ukk_poly.pairEncode rest_poly) using 1
  funext v
  simp [trial]

/-- The unary value of the trial is polynomial-time. -/
theorem unum_poly {U : List Bool → List Bool} (hU : PolyTimeComputable U) :
    PolyTimeComputable (unum U) :=
  hU.comp ((uM_poly.append uM_poly).pairEncode trial_poly)

/-- The acceptance test is polynomial-time. -/
theorem acc_poly {U : List Bool → List Bool} (hU : PolyTimeComputable U) :
    PolyTimeComputable fun v => [acc U v] :=
  polyTimeComputable_and (StateLoop.lenLe_comp rest_poly ukk_poly)
    (polyTimeComputable_not (StateLoop.lenLe_comp (unum_poly hU) uM_poly))

/-- Re-pairing the first component of a word with a shorter second component does not lengthen a
pair, and gives a word of length `2` on a non-pair. -/
theorem length_pairEncode_pairFstD_le (v s : List Bool) (hs : s.length ≤ (pairSndD v).length) :
    (pairEncode (pairFstD v) s).length ≤ max v.length 2 := by
  cases hv : pairDecode v with
  | none =>
    simp only [pairFstD_eq, pairSndD_eq, hv, Option.map_none, Option.getD_none, List.length_nil,
      nonpos_iff_eq_zero, List.length_eq_zero_iff] at hs ⊢
    subst hs
    simp [length_pairEncode]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have := eq_pairEncode_of_pairDecode v a b hv
    subst this
    simp only [pairFstD_pairEncode, pairSndD_pairEncode] at hs ⊢
    rw [length_pairEncode, length_pairEncode]
    omega

/-- The orbit of every word stays within `|v| + 2`. -/
theorem length_iterate_le (v : List Bool) (t : ℕ) : (step^[t] v).length ≤ v.length + 2 := by
  have key : ∀ t, (step^[t] v).length ≤ max v.length 2 := by
    intro t
    induction t with
    | zero => exact le_max_left _ _
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      refine (length_pairEncode_pairFstD_le _ _
        (by rw [List.length_drop]; exact Nat.sub_le _ _)).trans ?_
      exact max_le (ih.trans (le_refl _)) (le_max_right _ _)
  exact (key t).trans (by omega)

/-- The orbit on a genuine input: after `t` rounds, `t` trials have been dropped. -/
theorem iterate_step_start (kk M : ℕ) (L : List Bool) (t : ℕ) :
    step^[t] (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) L) =
      pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (L.drop (t * kk)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, rest, ukk, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
      List.drop_drop]
    congr 2
    ring

end PosLoop

/-- A trial succeeds iff its value is below `m`. -/
theorem isSome_uniformFromBits {m k : ℕ} (b : Fin k → Bool) :
    (uniformFromBits m k b).isSome = decide (bitsToNat b < m) := by
  simp only [uniformFromBits_def]
  split_ifs with h <;> simp [h]

/-- **The position sampler** [PS10, Algorithm 38.5, "`i ← [m]`", by rejection (D10)]: a
polynomial-time `Pm` with `Pm ⟨⟨1^k, 1^m⟩, trials⟩ = 1^i` where `i` is the output of
`rejectionSample m k n` on the `n` trials of `k` bits encoded in `trials` (`0` on failure),
for `0 < m`, `0 < k` and `2^k ≤ 2m`.

**Proof sketch.** `Complexity.polyTimeComputable_iterateFind` with `R := var` on the state word
`⟨⟨1^k, 1^m⟩, rest⟩` (`PosLoop`): each round drops one trial; the test accepts when a full
trial remains and its unary value (`exists_unaryOf` with pad `1^{2m}`, valid since the value is
below `2^k ≤ 2m`) is shorter than `1^m`; the payload is that unary value. The orbit of every
word is bounded by `|v| + 2` (`PosLoop.length_iterate_le`). On a genuine input the test at
round `t < n` is `bitsToNat (trial t) < m` and fails from round `n` on (no full trial remains),
so the loop's `find?` is the `find?` over `finRange n` (`find?_range_eq_map_find?_finRange`),
which is the `findSome?` of `rejectionSample` (`findSome?_eq_bind_find?`,
`isSome_uniformFromBits`). -/
theorem exists_posMachine : ∃ Pm : List Bool → List Bool, PolyTimeComputable Pm ∧
    ∀ (M kk n : ℕ) (hM : 0 < M), 0 < kk → 2 ^ kk ≤ 2 * M → ∀ pb' : Fin (n * kk) → Bool,
      Pm (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb')) =
        List.replicate
          ((rejectionSample M kk n fun t j => pb' (finProdFinEquiv (t, j))).getD ⟨0, hM⟩).val true := by
  obtain ⟨U, hU, hUspec⟩ := exists_unaryOf
  have horbit : ∀ (v : List Bool) (t : ℕ), t ≤ PolyExpr.var.eval v.length →
      (PosLoop.step^[t] v).length ≤ (PolyExpr.add .var (.const 2)).eval v.length := by
    intro v t _
    simpa using PosLoop.length_iterate_le v t
  have hfind := polyTimeComputable_iterateFind PosLoop.step_poly (PosLoop.acc_poly hU)
    (PosLoop.unum_poly hU) .var _ horbit
  refine ⟨_, hfind, fun M kk n hM hkk h2 pb' => ?_⟩
  have hunum : ∀ t : Fin n, PosLoop.unum U (PosLoop.step^[(t : ℕ)]
      (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb'))) =
      List.replicate (bitsToNat fun j => pb' (finProdFinEquiv (t, j))) true := by
    intro t
    rw [PosLoop.iterate_step_start]
    simp only [PosLoop.unum, PosLoop.uM, PosLoop.trial, PosLoop.rest, PosLoop.ukk,
      pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
    rw [← ofFn_block_eq_take_drop pb' t, hUspec]
    · rw [bitsToNat_eq_bitListToNat]
    · rw [List.length_append, List.length_replicate]
      have := bitsToNat_lt fun j => pb' (finProdFinEquiv (t, j))
      rw [bitsToNat_eq_bitListToNat] at this
      omega
  have hacc : ∀ t : ℕ, PosLoop.acc U (PosLoop.step^[t]
      (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb'))) =
      if h : t < n then decide (bitsToNat (fun j => pb' (finProdFinEquiv (⟨t, h⟩, j))) < M)
      else false := by
    intro t
    split_ifs with h
    · have := hunum ⟨t, h⟩
      simp only at this
      unfold PosLoop.acc
      rw [this, PosLoop.iterate_step_start]
      simp only [PosLoop.ukk, PosLoop.uM, PosLoop.rest, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate, List.length_drop, List.length_ofFn]
      have hmul : (t + 1) * kk ≤ n * kk := Nat.mul_le_mul_right kk h
      rw [Nat.add_mul, Nat.one_mul] at hmul
      have h1 : kk ≤ n * kk - t * kk := by omega
      simp [h1, ← decide_not]
    · unfold PosLoop.acc
      rw [PosLoop.iterate_step_start]
      have hmul : n * kk ≤ t * kk := Nat.mul_le_mul_right kk (not_lt.1 h)
      simp only [PosLoop.ukk, PosLoop.rest, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate, List.drop_eq_nil_of_le (List.length_ofFn.trans_le hmul),
        List.length_nil]
      simp [Nat.pos_iff_ne_zero.1 hkk]
  have hR : n ≤ PolyExpr.var.eval
      (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb')).length + 1 := by
    have := Nat.le_mul_of_pos_right n hkk
    simp only [PolyExpr.eval_var, length_pairEncode, List.length_replicate, List.length_ofFn]
    omega
  rw [find?_range_eq_map_find?_finRange hR
    (fun t : Fin n => decide (bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M)) _
    (fun t h => by rw [hacc, dif_pos h]) (fun t h => by rw [hacc, dif_neg (not_lt.2 h)])]
  have hrs : rejectionSample M kk n (fun t j => pb' (finProdFinEquiv (t, j))) =
      ((List.finRange n).find? fun t => decide (bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M)).bind
        fun t => uniformFromBits M kk fun j => pb' (finProdFinEquiv (t, j)) := by
    simp only [rejectionSample_def]
    rw [findSome?_eq_bind_find?]
    congr 2
    funext t
    exact isSome_uniformFromBits _
  rw [hrs]
  cases hf : (List.finRange n).find? fun t =>
      decide (bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M) with
  | none => simp
  | some t =>
    have ht : bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M := by
      simpa using List.find?_some hf
    simp only [Option.map_some, Option.bind_some]
    rw [hunum]
    simp only [uniformFromBits_def]
    rw [dif_pos ht]
    rfl

end TCSlib.Cryptography.OneWay

## ===== TCSlib/Cryptography/Asymptotic/UniversalPadding.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.UniversalLemmas
import TCSlib.Cryptography.Asymptotic.UniversalPadding.Parameter
import TCSlib.Cryptography.Asymptotic.UniversalPadding.BinaryRoot
import TCSlib.Cryptography.Asymptotic.UniversalPadding.Machine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The padded strong one-way function of Lemma 64.3

Proof infrastructure for [PS10, Lemma 64.3] (`TCSlib.Cryptography.lemma_64_3`): from a strong
one-way family `𝓕` with evaluator `F`, the padded family `PadQuad.family F ℓ d` with
`inLen = var`, `outLen = 2·var` and

`g'_m(y) = (y.drop ℓ(ν m) ++ F ⟨1^{ν m}, y.take ℓ(ν m)⟩) ++ 0^*` (`2m` bits),

where `ν m = max {n ≤ m : n^d ≤ m}` (`PadQuad.nu`) recovers the parameter from the input
length. For `d` dominating `ℓ`, `𝓕.outLen` and the running time of `F` (`exists_pow_dominates`),
the data block and the `F`-call fit in the input (`ℓ(ν m) + L(ν m) ≤ (ν m)^d ≤ m`), so the
padding is lossless and `g'` inherits one-wayness (`PadQuad.strongOneWay`, the reduction
`B(1^n, f(b)) = A'(1^m, ⟨a, f(b)⟩ padded).take ℓ(n)` with the padding sampled from the coins,
[Gar26, Lemma 2.3]); a linear-time multitape evaluator (`PadQuad.exists_linearTime_gStr`) gives a quadratic-time one-work-tape binary machine through
`Turing.FinTM.one_work_tape_binary` and `Turing.exists_codeTM` (`PadQuad.quadraticCode_of_linear`).

**Deviation:** the text defines `g'` on lengths `m = n^c` only; here every length `m` is
handled through `ν` (data first, padding after, zero-filled to `2m` bits), see the docstring of
`TCSlib.Cryptography.lemma_64_3`.

## Contents

* `UniversalPadding.Parameter` — the recovered parameter and its bounds.
* `UniversalPadding.BinaryRoot` — the binary computation of the shifted parameter.
* `UniversalPadding.Machine` — the linear-time word evaluator.

## Main definitions

* `TCSlib.Cryptography.PadQuad.nu` — the parameter recovered from the input length;
  `TCSlib.Cryptography.PadQuad.raw`, `PadQuad.gStr`, `PadQuad.family` — the padded function.

## Main results

* `TCSlib.Cryptography.PadQuad.exists_pow_dominates` — `p(n) ≤ n^d` eventually.
* `TCSlib.Cryptography.PadQuad.easy_of_linear`, `PadQuad.quadraticCode_of_linear` — the two
  computability clauses from the linear-time evaluator.
* `TCSlib.Cryptography.PadQuad.exists_linearTime_gStr` — the linear-time evaluator.
* `TCSlib.Cryptography.PadQuad.strongOneWay`, `TCSlib.Cryptography.PadQuad.exists_family` —
  one-wayness of the padded family and the statement of [PS10, Lemma 64.3] with
  `QuadraticCode` unfolded.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.13, Lemma 64.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.4 (Lemma 2.3, padding).
-/

namespace TCSlib.Cryptography.PadQuad

open Complexity Turing TCSlib.Cryptography

/-! ## Polynomial domination -/

/-- Every syntactic polynomial is eventually dominated by a power: `p(n) ≤ n^d` for
`n ≥ n₁`, with `d ≥ 1` (`d := c + 1` and `n₁ := C 2^c + 1` for the majorant `C (n + 1)^c`). -/
theorem exists_pow_dominates (p : PolyExpr) : ∃ d n₁ : ℕ, 1 ≤ d ∧ ∀ n ≥ n₁, p.eval n ≤ n ^ d := by
  obtain ⟨C, c, h⟩ := p.eval_le
  refine ⟨c + 1, C * 2 ^ c + 1, by omega, fun n hn => ?_⟩
  calc p.eval n ≤ C * (n + 1) ^ c := h n
    _ ≤ C * (2 * n) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)
    _ = (C * 2 ^ c) * n ^ c := by rw [mul_pow]; ring
    _ ≤ n * n ^ c := Nat.mul_le_mul_right _ (by omega)
    _ = n ^ (c + 1) := by ring

/-! ## The padded function -/

/-- The raw output of `g'` on `z` (`|z| = m`, `n = ν m`): the padding block `z.drop ℓ(n)`
followed by `F ⟨1^n, z.take ℓ(n)⟩` (data first, so that the split is a `pairSplitAt`). -/
def raw (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (z : List Bool) : List Bool :=
  z.drop (ℓ.eval (nu d z.length)) ++
    F (NUPPT.advInput (nu d z.length) (z.take (ℓ.eval (nu d z.length))))

/-- The string function of the padded family: the raw output zero-filled (or truncated) to
`2|z|` bits. -/
def gStr (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (z : List Bool) : List Bool :=
  (raw F ℓ d z ++ List.replicate (2 * z.length) false).take (2 * z.length)

/-- `gStr` has exactly `2|z|` bits. -/
theorem length_gStr (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (z : List Bool) :
    (gStr F ℓ d z).length = 2 * z.length := by
  simp only [gStr, List.length_take, List.length_append, List.length_replicate]
  omega

/-- `gStr` is length-regular with output length `2·var`. -/
theorem lengthRegular_gStr (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) :
    FunFamily.LengthRegular (gStr F ℓ d) (.mul (.const 2) .var) := fun z => by
  simp [length_gStr]

/-- **The padded family** `g'` of [PS10, Lemma 64.3]: `FunFamily.ofString` of `gStr` with
output length `2·var` (so `inLen = var`). -/
def family (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) : FunFamily :=
  FunFamily.ofString (gStr F ℓ d) (.mul (.const 2) .var)

/-- The input length of the padded family is the parameter. -/
theorem family_inLen (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) :
    (family F ℓ d).inLen = .var := rfl

/-- The encoding of the padded family's value is `gStr`. -/
theorem ofFn_family_f (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (m : ℕ)
    (x : Fin ((family F ℓ d).inLen.eval m) → Bool) :
    List.ofFn ((family F ℓ d).f m x) = gStr F ℓ d (List.ofFn x) :=
  FunFamily.ofFn_ofString_apply (lengthRegular_gStr F ℓ d) m x

/-! ## The computability clauses -/

/-- The padded family has a linear-time multitape evaluator.
[PS10, Lemma 64.3, the quadratic-time computation of the padded function]
Given a machine for F within C (k + 1)^c and a fixed degree dominating the
data length and the call cost, the evaluator computes gStr in linear time.

**Proof sketch.** Compute the input length in binary and recover the shifted
root by interval halving. At degree one, a single transducer suffices.
At larger degrees, the emitting loop converts the canonical binary root
to unary within a quadratic bound in the root, which fits the input length.
Evaluate the syntactic length polynomial on the shifted unary word using
the sharp monomial emitter. Restore the root's token and split the data.
The timed payload map retains the suffix while applying F to its actual
encoded argument. Concatenate the suffix, result and zeros, and cut to
twice the input length. The image bounds cover every length, including
the empty word and parameters below the domination threshold. -/
theorem exists_linearTime_gStr {F : List Bool → List Bool} {M : FinTM Bool} {C c : ℕ}
    (hM : M.ComputesFunInTime F fun k => C * (k + 1) ^ c) (ℓ : PolyExpr) {d n₁ : ℕ}
    (hd : 1 ≤ d) (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d) :
    ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1) := by
  simpa only [gStr, raw] using exists_linearTime_padded hM ℓ hd hdom

/-- **`g'` is easy to compute** from a linear-time evaluator: the evaluator on `⟨1^m, y⟩`
applies `gStr` to the second component (`ofFn_family_f`). -/
theorem easy_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {d : ℕ}
    (h : ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1)) :
    (family F ℓ d).Easy := by
  have hg : PolyTimeComputable (gStr F ℓ d) := polyTimeComputable_of_linear h
  refine (FunFamily.easy_iff _).2
    ⟨fun z => gStr F ℓ d (pairSndD z), hg.comp polyTimeComputable_pairSndD, fun m x => ?_⟩
  rw [ofFn_family_f, NUPPT.advInput_eq]
  exact congrArg (gStr F ℓ d) (pairSndD_pairEncode _ _)

/-- **`g'` is computable by a coded machine in quadratic time** from a linear-time multitape
evaluator: `Turing.FinTM.one_work_tape_binary` gives a one-work-tape binary machine within
`c₁ (c' (m + 1) + 1)² ≤ c₁ (c' + 1)² (m + 1)²`, and `Turing.exists_codeTM` a `CodeTM` with the
same runs. -/
theorem quadraticCode_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {d : ℕ}
    (h : ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1)) :
    ∃ (Mc : CodeTM) (c₀ : ℕ), ∀ m (x : Fin ((family F ℓ d).inLen.eval m) → Bool),
      Mc.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn ((family F ℓ d).f m x))
        (c₀ * (m + 1) ^ 2) := by
  obtain ⟨M', c', hM'⟩ := h
  obtain ⟨M₁, c₁, hk, hM₁⟩ := FinTM.one_work_tape_binary M' _ _ hM'
  obtain ⟨Mc, hMc⟩ := exists_codeTM M₁ hk
  refine ⟨Mc, c₁ * (c' + 1) ^ 2, fun m x => ?_⟩
  rw [ofFn_family_f, hMc]
  refine ((FinTM.computesFunInTime_iff _ _ _).1 hM₁ (List.ofFn x)).mono ?_
  rw [List.length_ofFn, family_inLen, PolyExpr.eval_var]
  calc c₁ * (c' * (m + 1) + 1) ^ 2 ≤ c₁ * ((c' + 1) * (m + 1)) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [Nat.add_mul, Nat.one_mul]; omega) 2)
    _ = c₁ * (c' + 1) ^ 2 * (m + 1) ^ 2 := by ring

/-! ## One-wayness of the padded family -/

/-- The encoding of a pair of strings assembled by `Fin.appendEquiv` (and a length cast) is
the concatenation of the encodings. -/
private theorem ofFn_appendEquiv {a b n : ℕ} (h : a + b = n) (q : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn (((Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool))) q) =
      List.ofFn q.1 ++ List.ofFn q.2 := by
  show List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) (Fin.append q.1 q.2)) = _
  rw [ofFn_arrowCongr_finCongr, List.ofFn_fin_append]

/-- The encoding of a coin string reassembled by `splitCoins` (and a length cast) is the
concatenation of the encodings of the halves. -/
private theorem ofFn_splitCoins_symm_cast {a b n : ℕ} (h : a + b = n)
    (q : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn (((splitCoins a b).symm.trans (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool))) q) =
      List.ofFn q.1 ++ List.ofFn q.2 := by
  show List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) ((splitCoins a b).symm q)) = _
  rw [ofFn_arrowCongr_finCongr]
  obtain ⟨q₁, q₂⟩ := q
  exact ofFn_splitCoins_symm a b q₁ q₂

section Hardness

variable {𝓕 : FunFamily} {F : List Bool → List Bool}
  (hFx : ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x))
  {d : ℕ} (hd : 1 ≤ d)

include hFx in
/-- The raw output on `b ++ a` (`|b| = ℓ(n)`, `|a| = m − ℓ(n)`, `ν m = n`) is `a ++ f_n(b)`. -/
theorem raw_eq {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (b : Fin (𝓕.inLen.eval n) → Bool) (a : Fin (m - 𝓕.inLen.eval n) → Bool) :
    raw F 𝓕.inLen d (List.ofFn b ++ List.ofFn a) = List.ofFn a ++ List.ofFn (𝓕.f n b) := by
  have hlen : (List.ofFn b ++ List.ofFn a).length = m := by
    simp only [List.length_append, List.length_ofFn]
    omega
  simp only [raw, hlen, hnu, List.take_left' (List.length_ofFn (f := b)),
    List.drop_left' (List.length_ofFn (f := b)), hFx]

include hFx in
/-- The padded output on `b ++ a` is `a ++ f_n(b)` followed by zeros (lossless padding, as
`(m − ℓ(n)) + L(n) ≤ 2m`). -/
theorem gStr_eq {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (hL : 𝓕.outLen.eval n ≤ m) (b : Fin (𝓕.inLen.eval n) → Bool)
    (a : Fin (m - 𝓕.inLen.eval n) → Bool) :
    gStr F 𝓕.inLen d (List.ofFn b ++ List.ofFn a) = (List.ofFn a ++ List.ofFn (𝓕.f n b)) ++
      List.replicate (2 * m - (List.ofFn a ++ List.ofFn (𝓕.f n b)).length) false := by
  have hlen : (List.ofFn b ++ List.ofFn a).length = m := by
    simp only [List.length_append, List.length_ofFn]
    omega
  unfold gStr
  rw [raw_eq hFx hnu hℓ b a, hlen, take_append_replicate_of_le]
  simp only [List.length_append, List.length_ofFn]
  omega

include hFx in
/-- The challenge the reduction hands to the inverter of `g'`: the padding evaluator on
`⟨1^m, a ++ f_n(b)⟩` is the encoding of `g'_m(b ++ a)`. -/
theorem padStr_eq_gStr {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (b : Fin (𝓕.inLen.eval n) → Bool) (a : Fin (m - 𝓕.inLen.eval n) → Bool) :
    padStr (.mul (.const 2) .var) (List.replicate m true)
      (List.ofFn a ++ List.ofFn (𝓕.f n b)) = gStr F 𝓕.inLen d (List.ofFn b ++ List.ofFn a) := by
  have hlen : (List.ofFn b ++ List.ofFn a).length = m := by
    simp only [List.length_append, List.length_ofFn]
    omega
  unfold gStr
  simp only [padStr_eq]
  rw [raw_eq hFx hnu hℓ b a, hlen]
  simp

include hFx in
/-- **Padding is injective on the data block**: equal padded outputs on `b' ++ a'` and
`b ++ a` force `f_n(b') = f_n(b)` (`List.append_inj` on the equal-length blocks). -/
theorem f_eq_of_gStr_eq {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (hL : 𝓕.outLen.eval n ≤ m) (b b' : Fin (𝓕.inLen.eval n) → Bool)
    (a a' : Fin (m - 𝓕.inLen.eval n) → Bool)
    (h : gStr F 𝓕.inLen d (List.ofFn b' ++ List.ofFn a') =
      gStr F 𝓕.inLen d (List.ofFn b ++ List.ofFn a)) : 𝓕.f n b' = 𝓕.f n b := by
  rw [gStr_eq hFx hnu hℓ hL b' a', gStr_eq hFx hnu hℓ hL b a, List.append_assoc,
    List.append_assoc] at h
  obtain ⟨-, h2⟩ := List.append_inj h (by simp)
  exact List.ofFn_injective (List.append_inj_left h2 (by simp))

include hFx in
/-- **The padding reduction wins** [Gar26, Lemma 2.3, machine form]: if `A` at parameter `n`
samples the padding `a` from its first `p(n)` coins, hands `A'` (at the length `m` with
`ν m = n`) the padded `⟨a, f_n(b)⟩` and returns the first `ℓ(n)` bits of the answer, then `A`
inverts `f` at `n` at least as often as `A'` inverts `g'` at `m`.

**Proof sketch.** `invProbAt_eq_uprob` on both sides. Split the uniform input of `g'` as
`(b, a)` (`Fin.appendEquiv`); split `A`'s coins as `((a, a''), (ρ, ρ''))` (`splitCoins`, with
`A'.coins m ≤ A'.coins (p n)` by `PolyExpr.eval_mono`); the extra coins `a'', ρ''` are unread
(`uprob_fst`). On `((b, a), ρ)`, `A`'s challenge to `A'` is `g'_m(b ++ a)` (`padStr_eq_gStr`),
so an answer `x' = b' ++ a'` of `A'` with `g'_m(x') = g'_m(b ++ a)` gives `A`'s answer `b'` with
`f_n(b') = f_n(b)` (`f_eq_of_gStr_eq`); conclude by `uprob_mono`. -/
theorem invProbAt_family_le (A' A : NUPPT) {n m : ℕ} (hnu : nu d m = n)
    (hℓ : 𝓕.inLen.eval n ≤ m) (hL : 𝓕.outLen.eval n ≤ m) {p : PolyExpr} (hm : m ≤ p.eval n)
    (hAc : A.coins = .add p (A'.coins.subst p))
    (hA : ∀ y (r : List Bool), A.runAtL n y r =
      (A'.runAtL m (padStr (.mul (.const 2) .var) (List.replicate m true)
        ((r.take (p.eval n)).take (m - 𝓕.inLen.eval n) ++ y))
        ((r.drop (p.eval n)).take (A'.coinLen m))).take (𝓕.inLen.eval n)) :
    (family F 𝓕.inLen d).invProbAt A' m ≤ 𝓕.invProbAt A n := by
  have hcast₁ : 𝓕.inLen.eval n + (m - 𝓕.inLen.eval n) = m := by omega
  let e : (Fin (𝓕.inLen.eval n) → Bool) × (Fin (m - 𝓕.inLen.eval n) → Bool) ≃ (Fin m → Bool) :=
    (Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hcast₁) (Equiv.refl Bool))
  have hofn : ∀ q, List.ofFn (e q) = List.ofFn q.1 ++ List.ofFn q.2 := fun q =>
    ofFn_appendEquiv hcast₁ q
  have hc₁ : A'.coinLen m ≤ A'.coinLen (p.eval n) := A'.coins.eval_mono hm
  have hcast₂ : (m - 𝓕.inLen.eval n) + (p.eval n - (m - 𝓕.inLen.eval n)) = p.eval n := by omega
  have hcast₃ : A'.coinLen m + (A'.coinLen (p.eval n) - A'.coinLen m) = A'.coinLen (p.eval n) := by
    omega
  have hcast₄ : p.eval n + A'.coinLen (p.eval n) = A.coinLen n := by
    simp [NUPPT.coinLen_eq, hAc, PolyExpr.eval_subst]
  let eA : (Fin (m - 𝓕.inLen.eval n) → Bool) × (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool) ≃
      (Fin (p.eval n) → Bool) :=
    (splitCoins _ _).symm.trans (Equiv.arrowCongr (finCongr hcast₂) (Equiv.refl Bool))
  let eR : A'.Coins m × (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool) ≃
      (Fin (A'.coinLen (p.eval n)) → Bool) :=
    (splitCoins _ _).symm.trans (Equiv.arrowCongr (finCongr hcast₃) (Equiv.refl Bool))
  let eC : ((Fin (m - 𝓕.inLen.eval n) → Bool) × (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool)) ×
      (A'.Coins m × (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool)) ≃ A.Coins n :=
    (Equiv.prodCongr eA eR).trans
      ((splitCoins _ _).symm.trans (Equiv.arrowCongr (finCongr hcast₄) (Equiv.refl Bool)))
  have hofnC : ∀ q, List.ofFn (eC q) =
      (List.ofFn q.1.1 ++ List.ofFn q.1.2) ++ (List.ofFn q.2.1 ++ List.ofFn q.2.2) := by
    intro q
    show List.ofFn (((splitCoins _ _).symm.trans
      (Equiv.arrowCongr (finCongr hcast₄) (Equiv.refl Bool))) (eA q.1, eR q.2)) = _
    rw [ofFn_splitCoins_symm_cast]
    show List.ofFn (eA q.1) ++ List.ofFn (eR q.2) = _
    rw [ofFn_splitCoins_symm_cast, ofFn_splitCoins_symm_cast]
  let eArr : (((Fin (𝓕.inLen.eval n) → Bool) × (Fin (m - 𝓕.inLen.eval n) → Bool)) × A'.Coins m) ×
      ((Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool) ×
        (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool)) ≃
      (Fin (𝓕.inLen.eval n) → Bool) ×
        (((Fin (m - 𝓕.inLen.eval n) → Bool) × (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool)) ×
          (A'.Coins m × (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool))) :=
    (Equiv.prodProdProdComm _ _ _ _).trans
      ((Equiv.prodCongr (Equiv.prodAssoc _ _ _) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
  rw [FunFamily.invProbAt_eq_uprob, FunFamily.invProbAt_eq_uprob,
    ← uprob_comp_equiv (Equiv.prodCongr e (Equiv.refl (A'.Coins m))),
    ← uprob_comp_equiv (eArr.trans (Equiv.prodCongr (Equiv.refl _) eC))]
  rw [← uprob_fst (β := (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool) ×
    (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool))]
  refine uprob_mono fun q hq => ?_
  obtain ⟨x', hx', hgx'⟩ := hq
  -- the components of `q`
  obtain ⟨⟨⟨b, a⟩, ρ⟩, ⟨a'', ρ''⟩⟩ := q
  -- the answer of `A'`, split as `b' ++ a'`
  obtain ⟨⟨b', a'⟩, hx'e⟩ : ∃ q', e q' = x' := ⟨e.symm x', e.apply_symm_apply x'⟩
  refine ⟨b', ?_, ?_⟩
  · show A.runAt n (List.ofFn (𝓕.f n b)) (eC ((a, a''), (ρ, ρ''))) = List.ofFn b'
    rw [NUPPT.runAt_eq, hofnC, hA]
    simp only [List.take_left' (by simp; omega : (List.ofFn a ++ List.ofFn a'').length = p.eval n),
      List.drop_left' (by simp; omega : (List.ofFn a ++ List.ofFn a'').length = p.eval n),
      List.take_left' (List.length_ofFn (f := a)), List.take_left' (List.length_ofFn (f := ρ))]
    rw [padStr_eq_gStr hFx hnu hℓ b a, ← hofn (b, a), ← ofFn_family_f, ← NUPPT.runAt_eq]
    have hx'' : A'.runAt m (List.ofFn ((family F 𝓕.inLen d).f m (e (b, a)))) ρ = List.ofFn x' := hx'
    rw [hx'', ← hx'e, hofn, List.take_left' (List.length_ofFn (f := b'))]
  · show 𝓕.f n b' = 𝓕.f n b
    have hg : (family F 𝓕.inLen d).f m (e (b', a')) = (family F 𝓕.inLen d).f m (e (b, a)) := by
      rw [hx'e]; exact hgx'
    have hg' := congrArg List.ofFn hg
    rw [ofFn_family_f, ofFn_family_f, hofn, hofn] at hg'
    exact f_eq_of_gStr_eq hFx hnu hℓ hL b b' a a' hg'

include hFx hd in
/-- **The padded family is strongly one-way** [PS10, Lemma 64.3, "`g'` is strongly one-way"],
given a linear-time evaluator (`hlin`) and `d` dominating `ℓ + L` from `n₁` on (`hdom`).

**Proof sketch.** *Easy* is `easy_of_linear`. *Hard:* let `A'` invert `g'` with probability
`≥ 1/m^e` at infinitely many `m` (`not_negligible_iff`). Call `m` good when `m ≥ n₁^d`,
`m ≥ 1` and `A'` is that successful at `m`; `φ n` is a good `m` with `ν m = n` when one exists
(else `0`), majorised by `p := (n + 1)^d` (`lt_succ_nu_pow`). The reduction `A` is
`NUPPT.exists_reparam_pre_post_adv A' φ p` with advice `⟨⟨1^{φ n}, 1^{φ n − ℓ(n)}⟩, 1^{ℓ(n)}⟩`,
pre-processing `⟨y, a⟩ ↦ padStr (2·var) 1^{φ n} (a.take (φ n − ℓ(n)) ++ y)` and post-processing
"the first `ℓ(n)` bits", behind `NUPPT.exists_split _ p` which samples the padding `a` from
the first `p(n)` coins. For every good `m` with `n := ν m ≥ max(n₀, 2^{de}, n₁)`,
`invProbAt_family_le` at `m' := φ n` gives `1/n^{de+1} ≤ 1/(n+1)^{de} ≤ 1/m'^e ≤ invProbAt A' m'
≤ 𝓕.invProbAt A n`, contradicting `h.hard A` at the degree `de + 1`. -/
theorem strongOneWay (h : 𝓕.StrongOneWay) {n₁ : ℕ}
    (hdom : ∀ n ≥ n₁, 𝓕.inLen.eval n + 𝓕.outLen.eval n ≤ n ^ d)
    (hlin : ∃ (M' : FinTM Bool) (c' : ℕ),
      M'.ComputesFunInTime (gStr F 𝓕.inLen d) fun m => c' * (m + 1)) :
    (family F 𝓕.inLen d).StrongOneWay where
  easy := easy_of_linear hlin
  hard A' := by
    classical
    by_contra hneg
    obtain ⟨e, he⟩ := not_negligible_iff.mp hneg
    let good : ℕ → Prop := fun m => n₁ ^ d ≤ m ∧ 1 ≤ m ∧
      1 / (m : ℝ) ^ e ≤ (family F 𝓕.inLen d).invProbAt A' m
    let φ : ℕ → ℕ := fun n => if h : ∃ m, good m ∧ nu d m = n then h.choose else 0
    let p : PolyExpr := .pow (.add .var (.const 1)) d
    have hφ : ∀ n, φ n ≤ p.eval n := by
      intro n
      simp only [φ, p, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
      split_ifs with hex
      · have h1 := hex.choose_spec.2
        have h2 := lt_succ_nu_pow hd hex.choose
        rw [h1] at h2
        exact h2.le
      · exact Nat.zero_le _
    have hφ_spec : ∀ n, (∃ m, good m ∧ nu d m = n) → good (φ n) ∧ nu d (φ n) = n := by
      intro n hex
      simp only [φ, dif_pos hex]
      exact hex.choose_spec
    let β : ℕ → List Bool := fun n => pairEncode
      (pairEncode (List.replicate (φ n) true) (List.replicate (φ n - 𝓕.inLen.eval n) true))
      (List.replicate (𝓕.inLen.eval n) true)
    have hβ : ∀ n, (β n).length ≤
        (PolyExpr.add (.add (.mul (.const 6) p) (.const 6)) 𝓕.inLen).eval n := by
      intro n
      have h1 := hφ n
      simp only [β, length_pairEncode, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_mul,
        PolyExpr.eval_const]
      omega
    have hpre : PolyTimeComputable fun w => padStr (.mul (.const 2) .var)
        (pairFstD (pairFstD (pairFstD w)))
        ((pairSndD (pairSndD w)).take (pairSndD (pairFstD (pairFstD w))).length ++
          pairFstD (pairSndD w)) := by
      have hu : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD w)) :=
        polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
      have hv : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
        polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
      have ha : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
        polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
      have hy : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
        polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
      have hcut : PolyTimeComputable fun w =>
          (pairSndD (pairSndD w)).take (pairSndD (pairFstD (pairFstD w))).length := by
        have h := (polyTimeComputable_pairTakePoly .var).comp (hv.pairEncode ha)
        convert h using 1
        funext w
        simp
      have h := (polyTimeComputable_padStr (.mul (.const 2) .var)).comp
        (hu.pairEncode (hcut.append hy))
      convert h using 1
      funext w
      simp
    have hpost : PolyTimeComputable fun w => (pairSndD w).take (pairSndD (pairFstD w)).length := by
      have h := (polyTimeComputable_pairTakePoly .var).comp
        ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode
          polyTimeComputable_pairSndD)
      convert h using 1
      funext w
      simp
    obtain ⟨B, hBc, hB⟩ := A'.exists_reparam_pre_post_adv φ p hφ β _ hβ hpre hpost
    obtain ⟨A, hAc, -, hA⟩ := B.exists_split p
    have hA' : ∀ n y (r : List Bool), A.runAtL n y r =
        (A'.runAtL (φ n) (padStr (.mul (.const 2) .var) (List.replicate (φ n) true)
          ((r.take (p.eval n)).take (φ n - 𝓕.inLen.eval n) ++ y))
          ((r.drop (p.eval n)).take (A'.coinLen (φ n)))).take (𝓕.inLen.eval n) := by
      intro n y r
      rw [hA, hB]
      simp [β]
    -- the contradiction with the one-wayness of `𝓕` at degree `d e + 1`
    obtain ⟨n₀, hn₀⟩ := (negligible_iff _).1 (h.hard A) (d * e + 1)
    obtain ⟨m, hm, hgm⟩ := he (max (max n₀ (2 ^ (d * e))) 1 ^ d + n₁ ^ d + 1)
    have hNd : max (max n₀ (2 ^ (d * e))) 1 ^ d ≤ m := by omega
    have hN : max (max n₀ (2 ^ (d * e))) 1 ≤ nu d m := le_nu hd hNd
    have hn₁ : n₁ ≤ nu d m := le_nu hd (by omega)
    have hgood : good m := ⟨by omega, by omega, by
      rwa [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)] at hgm⟩
    obtain ⟨hgood', hnu'⟩ := hφ_spec (nu d m) ⟨m, hgood, rfl⟩
    -- notation: `n := nu d m`, `m' := φ n`
    have hn_n₀ : n₀ ≤ nu d m := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
    have hn_pow : 2 ^ (d * e) ≤ nu d m :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
    have hn_one : 1 ≤ nu d m := le_trans (le_max_right _ _) hN
    have hℓL : 𝓕.inLen.eval (nu d m) + 𝓕.outLen.eval (nu d m) ≤ φ (nu d m) := by
      refine (hdom _ hn₁).trans ?_
      have h2 := nu_pow_le hd (φ (nu d m))
      rw [hnu'] at h2
      exact h2
    have hm'p : φ (nu d m) ≤ p.eval (nu d m) := hφ _
    have hAc' : A.coins = .add p (A'.coins.subst p) := by rw [hAc, hBc]
    have hcore := invProbAt_family_le hFx A' A hnu' (by omega) (by omega) hm'p hAc'
      (hA' (nu d m))
    have hbound := hn₀ (nu d m) hn_n₀
    rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)] at hbound
    have hsucc := hgood'.2.2
    -- real arithmetic: `1/n^(de+1) ≤ 1/(n+1)^(de) ≤ 1/m'^e`
    have hm'e : (φ (nu d m) : ℝ) ^ e ≤ ((nu d m : ℝ) + 1) ^ (d * e) := by
      have h1 : φ (nu d m) ^ e ≤ ((nu d m + 1) ^ d) ^ e := Nat.pow_le_pow_left hm'p e
      rw [← pow_mul] at h1
      exact_mod_cast h1
    have hnde : ((nu d m : ℝ) + 1) ^ (d * e) ≤ (nu d m : ℝ) ^ (d * e + 1) := by
      have h1 : (nu d m + 1) ^ (d * e) ≤ nu d m ^ (d * e + 1) := by
        calc (nu d m + 1) ^ (d * e) ≤ (2 * nu d m) ^ (d * e) :=
              Nat.pow_le_pow_left (by omega) _
          _ = 2 ^ (d * e) * nu d m ^ (d * e) := by rw [mul_pow]
          _ ≤ nu d m * nu d m ^ (d * e) := Nat.mul_le_mul_right _ hn_pow
          _ = nu d m ^ (d * e + 1) := by ring
      exact_mod_cast h1
    have hm'pos : (0 : ℝ) < (φ (nu d m) : ℝ) ^ e := by
      have : (1 : ℝ) ≤ (φ (nu d m) : ℝ) := by exact_mod_cast hgood'.2.1
      positivity
    have h1 : 1 / (nu d m : ℝ) ^ (d * e + 1) ≤ 1 / (φ (nu d m) : ℝ) ^ e :=
      one_div_le_one_div_of_le hm'pos (hm'e.trans hnde)
    linarith

end Hardness

/-- **[PS10, Lemma 64.3] with `QuadraticCode` unfolded**: from a strong one-way family, a
strong one-way family with `inLen = var` computable by a coded machine in time `c₀ (m + 1)²`
on the bare input — the padded family at the degree `d` of `exists_pow_dominates` applied to
`ℓ + L + (running time of the evaluator)`, using its linear-time evaluator
(`exists_linearTime_gStr`).

**Proof sketch.** `h.easy` gives `F` with machine `M` within `C (k + 1)^c`; dominate
`ℓ + L + C (2n + 3 + ℓ(n))^c` by `n^d` from `n₁` on (`exists_pow_dominates` on the syntactic
polynomial `add (add ℓ L) ((normal C c).subst (add (mul (const 2) var) (add (const 2) ℓ)))`);
`exists_linearTime_gStr` gives the linear evaluator; conclude with `strongOneWay` and
`quadraticCode_of_linear`. -/
theorem exists_family (h : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay) :
    ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧
      ∃ (M : CodeTM) (c₀ : ℕ), ∀ n (x : Fin (𝓖.inLen.eval n) → Bool),
        M.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (𝓖.f n x))
          (c₀ * (𝓖.inLen.eval n + 1) ^ 2) := by
  obtain ⟨𝓕, h⟩ := h
  obtain ⟨F, hF, hFx⟩ := (FunFamily.easy_iff 𝓕).1 h.easy
  obtain ⟨M, C, c, hM⟩ := (polyTimeComputable_iff F).1 hF
  obtain ⟨d, n₁, hd, hdom⟩ := exists_pow_dominates
    (.add (.add 𝓕.inLen 𝓕.outLen)
      ((PolyExpr.normal C c).subst (.add (.mul (.const 2) .var) (.add (.const 2) 𝓕.inLen))))
  have hdom₁ : ∀ n ≥ n₁, 𝓕.inLen.eval n + 𝓕.outLen.eval n ≤ n ^ d := fun n hn => by
    have := hdom n hn
    simp only [PolyExpr.eval_add] at this
    omega
  have hdom₂ : ∀ n ≥ n₁, 𝓕.inLen.eval n + C * (2 * n + 3 + 𝓕.inLen.eval n) ^ c ≤ n ^ d :=
    fun n hn => by
      have := hdom n hn
      simp only [PolyExpr.eval_add, PolyExpr.eval_subst, PolyExpr.eval_normal, PolyExpr.eval_mul,
        PolyExpr.eval_const, PolyExpr.eval_var] at this
      have h2 : C * (2 * n + 3 + 𝓕.inLen.eval n) ^ c = C * (2 * n + (2 + 𝓕.inLen.eval n) + 1) ^ c := by
        congr 2
        omega
      omega
  have hlin := exists_linearTime_gStr hM 𝓕.inLen hd hdom₂
  exact ⟨family F 𝓕.inLen d, family_inLen F 𝓕.inLen d, strongOneWay hFx hd h hdom₁ hlin,
    quadraticCode_of_linear hlin⟩


end TCSlib.Cryptography.PadQuad

## ===== TCSlib/Cryptography/Asymptotic/Adversary.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.HardcoreBit.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as adversaries of the concrete experiments

The bridge between the machine layer (`Complexity.NUPPT`, strings `List Bool`) and the
concrete security experiments of `TCSlib.Cryptography.Foundations.Experiments` (typed
inputs `Fin m → Bool`, adversaries as functions of the input and of a uniform coin string).
An `NUPPT` `A` activated at parameter `n` becomes

* an *inverter* `A.inverter n ℓ m : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)`
  [PS10, Definitions 27.3, 28.4]: `A(1^n, y)` with the output decoded as an `ℓ`-bit string;
* its literal variant `A.inverterLit ℓ m` for [PS10, Definition 26.1] (`A(f(x))`, activation
  at the input length `m`, no `1^n`);
* a *distinguisher* / *predictor* `A.distinguisher n m`, `A.predictor n m`
  [PS10, Definitions 69.4, 75.2, 78.3]: `A(1^n, t) = 1`, i.e. the output is the string `[true]`;
  `A.distinguisherL n` takes an untyped sample.

Inversion with a possibly failing decoder is `invProbOpt` (the probability that the decoded
output is a preimage); it is bridged to the concrete `invProb` by `invProbOpt_le_invProb`
(any default for a failure can only increase the probability) and `invProbOpt_some` (a total
inverter has the same probability). Foundation decision D5: inverses are sought in the
domain at the current parameter, and a wrong-length output counts as failure.

The file also records that "computes `f` with probability one" [PS10, Definition 24.6]
is, on the finite uniform coin space, the same as "for every coin string"
(`Complexity.NUPPT.computes_iff_uprob`), which justifies the frozen form of
`Complexity.NUPPT.Computes`.

**Deviation:** `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable
by `ifEq`).

## Main definitions

* `TCSlib.Cryptography.coinBlock` — the common indexed coin-tape segment.
* `TCSlib.Cryptography.decodeFin` — decode a string as an `ℓ`-bit string, failure on a wrong
  length; `TCSlib.Cryptography.padFin` — pad/truncate (for samplers).
* `TCSlib.Cryptography.blocksEquivX`, `TCSlib.Cryptography.FunFamily.blocks` — the canonical
  block bijection `(Fin (q·ℓ) → X) ≃ (Fin q → Fin ℓ → X)` and its Bool form, with the readers
  `blocksEquivX_apply`, `blocksEquivX_symm_apply`, `FunFamily.blocks_apply`,
  `FunFamily.blocks_symm_apply`.
* `Complexity.NUPPT.inverter`, `Complexity.NUPPT.inverterLit` — an `NUPPT` as an inverter
  (with `1^n`, and literal).
* `Complexity.NUPPT.distinguisher`, `Complexity.NUPPT.distinguisherL`,
  `Complexity.NUPPT.predictor` — an `NUPPT` as a distinguisher / predictor.
* `TCSlib.Cryptography.invProbOpt` — inversion probability of a possibly failing inverter.

## Main results

* `TCSlib.Cryptography.coinBlock_eq`, `TCSlib.Cryptography.length_coinBlock` — the segment
  equation and its full-length condition.
* `TCSlib.Cryptography.decodeFin_ofFn`, `TCSlib.Cryptography.padFin_ofFn` — decoding and
  padding invert `List.ofFn`; `TCSlib.Cryptography.decodeFin_eq_some_iff` — decoding succeeds
  exactly on the encoding; `TCSlib.Cryptography.ofFn_padFin_of_length` — padding a string of the
  right length keeps it.
* `TCSlib.Cryptography.ofFn_cast`, `TCSlib.Cryptography.ofFn_arrowCongr_finCongr` — a bit vector
  read across an equality of widths keeps its string.
* `TCSlib.Cryptography.FunFamily.ofFn_blocks` — block `j` of a string is its `j`-th window.
* `TCSlib.Cryptography.invProbOpt_le_invProb`, `TCSlib.Cryptography.invProbOpt_some` — the
  bridges to the concrete `invProb`.
* `TCSlib.Cryptography.invProbOpt_nonneg`, `TCSlib.Cryptography.invProbOpt_le_one` — bounds.
* `Complexity.NUPPT.computes_iff_uprob` — probability one is every coin string
  [PS10, Definition 24.6].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1–2.2: Definitions 24.6, 26.1, 27.3; §3.1–3.3: Definitions 69.4, 75.2, 78.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definitions 2.1, 2.3, 3.2–3.4 (the concrete experiments).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- The `i`-th segment of `B` bits of a coin string; a short final segment is truncated. -/
def coinBlock (B i : ℕ) (r : List Bool) : List Bool := (r.drop (i * B)).take B

/-- The defining equation of `coinBlock`: `coinBlock B i r = (r.drop (i·B)).take B`. -/
theorem coinBlock_eq (B i : ℕ) (r : List Bool) : coinBlock B i r = (r.drop (i * B)).take B := rfl

/-- A coin segment has exactly `B` bits when its end lies within the input tape. -/
theorem length_coinBlock {B i : ℕ} {r : List Bool} (h : (i + 1) * B ≤ r.length) :
    (coinBlock B i r).length = B := by
  simp only [coinBlock_eq, List.length_take, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

/-- Decode a string as an `ℓ`-bit string: `some` of its bits if the length is exactly `ℓ`,
`none` otherwise (a wrong-length answer of an inverter is a failure, D5). -/
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=
  if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none

/-- The defining equation of `decodeFin`: `decodeFin ℓ w` is `some` of the bits of `w` when
`|w| = ℓ`, and `none` otherwise. -/
theorem decodeFin_eq (ℓ : ℕ) (w : List Bool) :
    decodeFin ℓ w = if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none :=
  rfl

/-- Pad with `false` or truncate a string to exactly `ℓ` bits (the output convention of
samplers, where no failure is possible). -/
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i false

/-- The defining equation of `padFin`: `padFin ℓ w = fun i => w.getD i false`. -/
theorem padFin_def (ℓ : ℕ) (w : List Bool) :
    padFin ℓ w =
      (fun i => w.getD i false :
        Fin ℓ → Bool) := rfl

/-- Bit `i` of `padFin ℓ w` is bit `i` of `w`, default `false`. -/
theorem padFin_apply (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) : padFin ℓ w i = w.getD i false :=
  rfl

/-- Decoding the encoding of an `ℓ`-bit string returns it. -/
theorem decodeFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : decodeFin ℓ (List.ofFn x) = some x := by
  simp [decodeFin]

/-- A decoded string has exactly the decoded length. -/
theorem length_eq_of_decodeFin_eq_some {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
    (h : decodeFin ℓ w = some x) : w.length = ℓ := by
  by_contra hw
  simp [decodeFin, hw] at h

/-- **Decoding succeeds exactly on the encoding**: `decodeFin ℓ w = some x ↔ w = List.ofFn x`,
for every width `ℓ` (`ℓ = 0` included) and every string `w`.

**Proof sketch.** A successful decoding has `|w| = ℓ` (`length_eq_of_decodeFin_eq_some`); after
substituting the width, `w = List.ofFn (w.get ·)` (`List.ofFn_get`) decodes to the bits of `w`
(`decodeFin_ofFn`), which are therefore `x`. Conversely `decodeFin_ofFn`. -/
theorem decodeFin_eq_some_iff (ℓ : ℕ) (w : List Bool) (x : Fin ℓ → Bool) :
    decodeFin ℓ w = some x ↔ w = List.ofFn x := by
  constructor
  · intro h
    have hw := length_eq_of_decodeFin_eq_some h
    subst hw
    have h' := decodeFin_ofFn (fun j : Fin w.length => w.get j)
    rw [List.ofFn_get, h, Option.some.injEq] at h'
    rw [h']
    exact (List.ofFn_get w).symm
  · rintro rfl
    exact decodeFin_ofFn x

/-- Padding the encoding of an `ℓ`-bit string returns it. -/
theorem padFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padFin ℓ (List.ofFn x) = x := by
  funext i
  simp [padFin]

/-- The encoding of `padFin L w` is `w` when `|w| = L`: `List.ofFn (padFin L w) = w`. -/
theorem ofFn_padFin_of_length {L : ℕ} {w : List Bool} (hw : w.length = L) :
    List.ofFn (padFin L w) = w := by
  refine List.ext_getElem (by simp [hw]) fun j hj₁ hj₂ => ?_
  simp [padFin_def, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj₂]

/-! ### Bit vectors across equal widths -/

/-- Reading a bit vector across an equality of widths keeps its string:
`⟦cast h f⟧ = ⟦f⟧` when `a = b`. -/
theorem ofFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
  subst hab
  rfl

/-- Reading a vector at an equal width keeps its word:
`⟦(arrowCongr (finCongr h) (refl Bool)) v⟧ = ⟦v⟧`. -/
theorem ofFn_arrowCongr_finCongr {a b : ℕ} (h : a = b) (v : Fin a → Bool) :
    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) v) = List.ofFn v := by
  subst h
  rfl

/-! ### Blocks of a flat tuple -/

/-- A tuple of `q · ℓ` entries with values in an arbitrary type `X` as `q` consecutive blocks of
`ℓ` entries: block `i`, position `j` is entry `finProdFinEquiv (i, j) = j + ℓ·i` (Mathlib's
`finProdFinEquiv` and `Equiv.curry`). All `q`, `ℓ` (zero included). -/
def blocksEquivX (q ℓ : ℕ) (X : Type*) : (Fin (q * ℓ) → X) ≃ (Fin q → Fin ℓ → X) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl X)).trans (Equiv.curry _ _ _)

/-- The forward reader of `blocksEquivX`: block `i`, position `j` of `x` is entry
`finProdFinEquiv (i, j)` of `x`. -/
theorem blocksEquivX_apply (q ℓ : ℕ) {X : Type*} (x : Fin (q * ℓ) → X) (i : Fin q) (j : Fin ℓ) :
    blocksEquivX q ℓ X x i j = x (finProdFinEquiv (i, j)) := rfl

/-- The inverse of `blocksEquivX` reads block `p.divNat`, position `p.modNat`. -/
theorem blocksEquivX_symm_apply (q ℓ : ℕ) {X : Type*} (t : Fin q → Fin ℓ → X) (p : Fin (q * ℓ)) :
    (blocksEquivX q ℓ X).symm t p = t p.divNat p.modNat := rfl

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`): the encoding of the tuple `(x₁, …, x_q)` of
[PS10, Theorem 35.1] as the `q·ℓ`-bit concatenation; the Bool specialization of
`blocksEquivX`. -/
def FunFamily.blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  blocksEquivX q ℓ Bool

/-- The defining equation of `blocks`: block `i`, position `j` is position `ℓ·i + j` of `x`. -/
theorem FunFamily.blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) :=
  blocksEquivX_apply q ℓ x i j

/-- The inverse of `blocks` reads block `k.divNat`, position `k.modNat`. -/
theorem FunFamily.blocks_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (FunFamily.blocks q ℓ).symm t k = t k.divNat k.modNat :=
  blocksEquivX_symm_apply q ℓ t k

/-- **Block `j` is the `j`-th window of the string:**
`⟦FunFamily.blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ`.

**Proof sketch.** Block `j` ends within the string, `j·ℓ + ℓ ≤ q·ℓ`, so both sides have `ℓ` bits.
Position `k` of block `j` is position `finProdFinEquiv (j, k) = k + ℓ·j` of `ω`
(`FunFamily.blocks_apply`), which is position `k` of the window. -/
theorem FunFamily.ofFn_blocks (q ℓ : ℕ) (ω : Fin (q * ℓ) → Bool) (j : Fin q) :
    List.ofFn (FunFamily.blocks q ℓ ω j) = ((List.ofFn ω).drop (j * ℓ)).take ℓ := by
  have hle : (j : ℕ) * ℓ + ℓ ≤ q * ℓ := by
    have := Nat.mul_le_mul_right ℓ (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine (FunFamily.blocks_apply q ℓ ω j ⟨k, _⟩).trans ?_
    congr 1
    refine Fin.ext ?_
    rw [finProdFinEquiv_apply_val]
    show k + ℓ * j = j * ℓ + k
    rw [Nat.mul_comm]
    omega

/-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure
[PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`].

**Deviation:** wrong-length output = failure (D5). For a typed family this loses nothing. For
a string function `f : {0,1}* → {0,1}*` the text's experiment also accepts a preimage of
another length, so the typed experiment can count fewer successes and typed one-wayness is
implied by, but weaker than, the text's, unless `|f(x)|` determines `|x|` (length-regular `f`
whose output length is a non-constant `PolyExpr`, hence injective in the input length; with
constant output length neither notion is satisfiable). The proviso is stated where string functions enter the typed world,
`FunFamily.ofString` (`Asymptotic/OneWay.lean`; gate 03a, note 15). -/
def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)

/-- The defining equation of `NUPPT.inverter`: the output of `A(1^n, y; r)` decoded as an
`ℓ`-bit string, `A.inverter n ℓ m y r = decodeFin ℓ (A.runAt n (List.ofFn y) r)`. -/
theorem _root_.Complexity.NUPPT.inverter_def (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) : A.inverter n ℓ m y r = decodeFin ℓ (A.runAt n (List.ofFn y) r) := rfl

/-- The literal inverter `A(y)` of [PS10, Definition 26.1]: activation at parameter `|y| = m`
(the text gives the adversary `f(x)` only; the `1^{|y|}` prefix carries no information). -/
def _root_.Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt m (List.ofFn y) r)

/-- `A(1^n, t)` as a distinguisher: accepts iff the output is the string `[true]`
[PS10, Definition 69.4]. -/
def _root_.Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  fun t r => decide (A.runAt n (List.ofFn t) r = [true])

/-- `A(1^n, w)` as a distinguisher of untyped samples (ciphertexts, views, histories). -/
def _root_.Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool :=
  fun w r => decide (A.runAt n w r = [true])

/-- The defining equation of `distinguisherL`:
`A.distinguisherL n w r = decide (A.runAt n w r = [true])`. -/
theorem _root_.Complexity.NUPPT.distinguisherL_eq (A : NUPPT) (n : ℕ) (w : List Bool)
    (r : A.Coins n) : A.distinguisherL n w r = decide (A.runAt n w r = [true]) := rfl

/-- `A(1^n, y)` as a predictor of a bit: the same verdict convention as a distinguisher
[PS10, Definitions 75.2 and 78.3]. -/
def _root_.Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  A.distinguisher n m

/-- The literal inverter is the inverter at parameter `m`. -/
theorem _root_.Complexity.NUPPT.inverterLit_eq (A : NUPPT) (ℓ m : ℕ) :
    A.inverterLit ℓ m = A.inverter m ℓ m := rfl

/-- The typed distinguisher is the untyped one on `List.ofFn t`. -/
theorem _root_.Complexity.NUPPT.distinguisher_eq (A : NUPPT) (n m : ℕ) (t : Fin m → Bool)
    (r : A.Coins n) : A.distinguisher n m t r = A.distinguisherL n (List.ofFn t) r := rfl

/-- The predictor is the distinguisher. -/
theorem _root_.Complexity.NUPPT.predictor_eq (A : NUPPT) (n m : ℕ) :
    A.predictor n m = A.distinguisher n m := rfl

/-- The inverter succeeds on `(y, r)` iff the machine's output is the encoding of some `x'`. -/
theorem _root_.Complexity.NUPPT.inverter_eq_some_iff (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) (x' : Fin ℓ → Bool) :
    A.inverter n ℓ m y r = some x' ↔ A.runAt n (List.ofFn y) r = List.ofFn x' := by
  constructor
  · intro h
    have hw : (A.runAt n (List.ofFn y) r).length = ℓ := length_eq_of_decodeFin_eq_some h
    simp only [NUPPT.inverter, decodeFin, dif_pos hw, Option.some.injEq] at h
    subst h
    refine List.ext_get (by simp [hw]) fun i h₁ h₂ => ?_
    simp
  · intro h
    show decodeFin ℓ _ = _
    rw [h, decodeFin_ofFn]

/-- The probability that a possibly failing inverter `A`, given `f x` for uniform `x` and
uniform coins, outputs `some x'` with `f x' = f x` (the typed experiment of
[PS10, Definition 27.3] with a wrong-length output counted as failure, D5). -/
noncomputable def invProbOpt {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : ℝ :=
  uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1

/-- The defining equation of `invProbOpt`:
`invProbOpt f A = Pr_{(x, r)}[∃ x', A(f x, r) = some x' ∧ f x' = f x]`, over uniform
`(x, r) ∈ α × ρ`. -/
theorem invProbOpt_def {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A = uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1 := rfl

/-- Replacing a failure by any default can only increase the inversion probability: the
bridge from `invProbOpt` to the concrete `invProb` [Gar26, Definition 2.1]. -/
theorem invProbOpt_le_invProb {α β ρ : Type*} [Fintype α] [Fintype ρ] [Inhabited α] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default) := by
  rw [invProbOpt_def, invProb_def]
  refine uprob_mono ?_
  rintro ⟨x, r⟩ ⟨x', hx', hf⟩
  simp [hx', hf]

/-- A total inverter has the same probability under both conventions. -/
theorem invProbOpt_some {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → α) :
    invProbOpt f (fun y r => some (A y r)) = invProb f A := by
  unfold invProbOpt
  simp only [invProb_def]
  congr 1
  funext z
  simp

/-- The inversion probability is nonnegative. -/
theorem invProbOpt_nonneg {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : 0 ≤ invProbOpt f A :=
  uprob_nonneg _

/-- The inversion probability is at most one. -/
theorem invProbOpt_le_one {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : invProbOpt f A ≤ 1 :=
  uprob_le_one _

/-- **"With probability one" is "for every coin string"** [PS10, Definition 24.6]: `A`
computes `f` in the frozen sense (`Complexity.NUPPT.Computes`, equality for every coin
string) iff at every parameter and argument the event `A(1^n, y; r) = f(⟨1^n, y⟩)` has
probability one over the uniform coins. (On a finite uniform space an event of probability
one is the whole space, `HardcoreBit.forall_of_uprob_eq_one`.) -/
theorem _root_.Complexity.NUPPT.computes_iff_uprob (A : NUPPT) (f : List Bool → List Bool) :
    A.Computes f ↔
      ∀ n y, uprob (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = 1 := by
  rw [NUPPT.computes_iff]
  constructor
  · intro h n y
    have hp : (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = fun _ => True :=
      funext fun r => propext ⟨fun _ => trivial, fun _ => h n y r⟩
    rw [hp, uprob_true]
  · intro h n y r
    exact HardcoreBit.forall_of_uprob_eq_one (h n y) r

end TCSlib.Cryptography
