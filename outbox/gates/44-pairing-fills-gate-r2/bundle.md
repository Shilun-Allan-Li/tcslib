## ===== pack-r2.md (this pack) =====

# Gate 44 · Pairing fills: T1 (#340) and T4 (#346) · round 2

The auditor is Codex, under the standing ruling of 2026-11-11. Round 1 was **HOLD** (0 blockers, 1 major, 1 minor,
1 note); its findings are `findings-r1.md`. It found no mathematical gap. This round checks the three resolutions: a
ruling (G44-01), one docstring landing edit on #346 (G44-02) and a pack correction (G44-03). It also checks the new
joint tree T44′ with its replay and seal evidence, and that nothing new is undisclosed. **Round 1's passes are not
re-audited:** the proofs, frozen statements, readers, LE-bb1m, the supplement seals, the replay at T44 and the axioms.
The round-1 pack (`pack-r1.md`) still defines the scope.

- **PR #340** (T1): unchanged, at `916afc25c21f5e52b4b01958186ad55d2f615fd1` (merge base
  `9e7a96481785d6cac4dea3b2e990c49ac278b060`). Its code is exactly what round 1 audited.
- **PR #346** (T4): new head **`98cb0e521a94e94c304c78348fb5d3033435a3ed`** = round 1's head
  `89a18a8225be1b76166af12a15179da291747783` plus one commit, **LE-g44** (branch `land/pairings-bb1-machine`; merge base
  still `7291f6b237fec75add1549c0992c174442180488`). Now 8 SSH-signed commits; 8 files, +2756/−17 against the merge base
  (round 1: +2741/−17).
- **Records pin:** `4f4a7592a54cf82fa04f96b83645d7936672614c`, the records tip at staging ("Records: G44-01 ruled"). It
  descends from round 1's pin `8f888790` and from the replay tip `1d1a9bb3`. The 19 records commits since `1d1a9bb3`
  change no code path (`checks/series-r2.txt`). This pack, the resolutions and the three dated report corrections of
  G44-01 are filed after the pin, in one staging commit: the records commit that carries `dispatch-r2.md`.
  `verification-r2.zip` holds byte copies of the corrections (`records/`).
- **The joint tree T44′** = records tip × #340 × #346′ = **`bee027f0903d531b3a43511cea16bfa123210291`**. All three merge
  orders are clean and give this tree (`checks/mergetrees-r2.txt`, `landing/mergetrees-r2.txt`; scratch commits, not
  pushed). Against the tip it changes exactly the 9 files of the two PRs, each blob-equal to its PR head. Against round
  1's **T44** `33681cb8` its code differs in **exactly the three LE-g44 files**, and `git diff T44 T44′` over the code
  paths equals the LE-g44 diff byte for byte.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`; `IB/` is
`AdvancedEncryption/IdentityBased/` and `BBM/` is `IB/BonehBoyenMachine/`.

## Round-1 findings, resolutions and evidence

| Finding | Resolution | Evidence | What round 2 decides |
|---|---|---|---|
| **G44-01** major: disclosed exact re-derivations without a recorded acceptance and repayment. They are T1's inline verdict identity (= `TrapdoorPredictor.decide_singleton_eq_true`) and #346's `poly_rU/rZ/rW/rS` (= `Games/Efficiency.lean:538–550`). Both reports say "nothing for the duplication ledger". | **Ruling G44-01 (Seyoon, 2026-11-17): accept; repay in cleanup Stage 2.** Ledger rows **DL-55** and **DL-56**, and the Stage 2 scope lines. Dated corrections under both reports' lines (kept as filed), and a note in the bb1-machine review. No code change. | Records `4f4a7592`: `duplication-ledger.md` rows 82–83, `cleanup-stages.md` § Stage 2, the plan's ruling row. Corrections: `records/corrections/` in `verification-r2.zip`. | § 1: are acceptance, shared home and repayment point recorded as policy §1 requires, and are both dispositions corrected? Closed? |
| **G44-02** minor: `[PS10, Theorem 52.3]` mis-locates the bounded sampler (`BBM/Draws.lean:58`, `:130`; the References entries of `Words.lean:60`, `Handler.lean:62`) | **LE-g44** `98cb0e52`, docstrings and comments only: the sampler and its bound are attributed to the library's `Candidates.sampleBelowL` and `Candidates.statClose_sampleBelowL`; PS10 §2.8 / Theorem 52.3 is kept as context only; the three References entries are corrected consistently | `le-g44.diff.txt`, `checks/le-r2.txt`, `checks/sources-r2.txt`, `sources-r2.zip` | § 2: comment-only; citation accurate; closed? |
| **G44-03** note: `pack-r1.md:339` doubled the `Assumptions` paired-control figures | Corrected here (§ 3) and in `resolutions-r1.md`. The round-1 pack stays as filed. | `checks/g44-03-controls.txt` (recount from round 1's raw logs) | § 3: are the corrected figures right? |

## What to check

### 1. G44-01: the acceptance and the corrected dispositions

No code changes for G44-01. The records (at the pin unless noted):
- **Ledger** (`briefs/pass-shelat-ch5-8/duplication-ledger.md`, rows 82–83).
  - **DL-55:** T1's inline verdict identity `decide ([b] = [true]) = b`, specialised to the solver-success bit
    (#340, `Pairing/Assumptions.lean:199`). Published form: `TrapdoorPredictor.decide_singleton_eq_true`
    (`Encryption/PublicKey/TrapdoorPredictor.lean:144`), in the public-key layer, which the pairing closure does not
    import. Accepted (Seyoon, 2026-11-17, Gate 44 G44-01). Repayment, **cleanup Stage 2:** promote
    `decide_singleton_eq_true` to a shared low-level home importable by both layers, then re-point `TrapdoorPredictor`
    and T1's proof (proof-only).
  - **DL-56:** `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` (#346, `BBM/Words.lean:261`–`271`). Published forms:
    `Games.polyTimeComputable_rU`, `_rZ`, `_rW`, `_rS` (`Games/Efficiency.lean:538–550`). Accepted, same ruling.
    Repayment, **cleanup Stage 2:** re-point the four to the `Games/Efficiency` facts, adding a reader there if the
    recorded obstruction needs one (proof-only).
- **Stage 2 scope** (`briefs/pass-shelat-ch5-8/cleanup-stages.md` § *Stage 2: re-point and prune*): a bullet names
  DL-55 and DL-56 with the shared home and the re-points. The gate of Stage 2 targets "every Pass–shelat ledger row
  closed".
- **The ruling** (`PairingCryptographyPlan.md`, last row at the pin): "Ruling G44-01 (Seyoon): accept, repay in cleanup
  Stage 2."
- **Corrections** (staging commit; byte copies in `records/corrections/`). Each original line is kept, and a dated
  block quote follows it:
  - `fills/pair-bdh/inhouse-r1/REPORT.md`, after line 99. Disclosure 5 re-derives the public identity; acceptance is
    DL-55.
  - `fills/bb1-machine/inhouse-r1/REPORT.md`, after line 260. Disclosure 1's four `poly_r*` re-prove the
    `Games/Efficiency` facts; the obstruction is recorded but acceptance was not; acceptance is DL-56.
  - `fills/bb1-machine/final-r1/review.md`, § *Duplication and reuse*: a dated sub-bullet. The review checked the
    worker's delta and took the checkpoint's overlap dispositions from the in-house REPORT without regrading them. That
    REPORT line is wrong for `poly_r*` (DL-56). The review's verdict is unchanged.
- **The PR descriptions.** Seyoon updates them before dispatch (drafts handed to Seyoon; § *Known slips*): #340's
  *Overlap and reuse* bullet says "7 disclosures, none a copy of a published lemma". It becomes: item 5 re-derives the
  published identity, disclosed and accepted as DL-55.

Do the ledger rows, the Stage 2 scope and the ruling record the explicit acceptance, the shared home and the repayment
point that policy §1 requires, for both families? Are the corrections accurate? Does this close G44-01?

### 2. G44-02: LE-g44 is comment-only, and the attribution is right

**The commit** (`checks/series-r2.txt`): `98cb0e52`, parent `89a18a82`, author and committer Claude. It has one SSH
signature (ed25519, `SHA256:32dP45eS…`), which verifies with the public key it carries. That key also signs the records
pin, and a one-byte tamper control fails. Files: `BBM/Draws.lean` +14/−5, `BBM/Words.lean` +4/−1, `BBM/Handler.lean`
+4/−1. **Not pushed at staging:** the maintainer pushes it to #346's branch before dispatch (§ *Known slips*).

**The edit, verbatim** (`le-g44.diff.txt` = `git diff 89a18a82 98cb0e52`, 6116 bytes, SHA-256 `e81b86c8…`):
- `Draws.lean`, module docstring (after "within `(1/2)^n` of uniform (`statClose_draw`)."):

  ```text
  The bounded sampler and
  its bound are the library's existing construction, `Candidates.sampleBelowL` and
  `Candidates.statClose_sampleBelowL` (`Cryptography/Candidates/DiscreteLog.lean`): for
  `0 < m < 2^n` its output on `n · n` uniform coins, with the fallback `0`, is within `(1/2)^n` of
  the uniform number below `m`.
  ```
- `Draws.lean`, `## References`. Old: `(Theorem 52.3, sampling Z_q by rejection; Definition 181.1, statistical
  closeness.)`. New:

  ```text
  (Definition 181.1, statistical closeness. Context only: §2.8, Theorem 52.3, the discrete-log
  collection, whose proof remarks that its domain `Z_q` is easy to sample; it does not give
  this sampler, its coin budget, its fallback or its bound, which are the library's
  `Candidates.sampleBelowL` and `Candidates.statClose_sampleBelowL`.)
  ```
- `Draws.lean`, `draw`'s docstring. Old: "**An exponent of `Z_p` drawn from `n · n` coins** [PS10, Theorem 52.3]: the
  rejection sampler `sampleBelowL p (Nat.size p) n n` with the fallback `0`, …". New:

  ```text
  /-- **An exponent of `Z_p` drawn from `n · n` coins**: the library's bounded rejection sampler
  `Candidates.sampleBelowL p (Nat.size p) n n` (`Cryptography/Candidates/DiscreteLog.lean`, whose
  bound `Candidates.statClose_sampleBelowL` gives `statClose_draw`) with the fallback `0`, read in
  `Z_p`, for the order `p` of the group described by `d` and `n = blockLen G κ`. That `Z_p` is
  easy to sample is the remark in the proof of [PS10, Theorem 52.3] (§2.8), context only. -/
  ```
- `Words.lean` and `Handler.lean`, `## References`, the same new text in both. Old: `(Algorithm 43.2, the extended
  Euclidean algorithm; Theorem 52.3, sampling Z_q.)`. New:

  ```text
  (Algorithm 43.2, the extended Euclidean algorithm. Context only: §2.8, Theorem 52.3, the
  discrete-log collection, whose proof remarks that its domain `Z_q` is easy to sample; it does
  not give the bounded sampler or its bound, which are the library's `Candidates.sampleBelowL`
  and `Candidates.statClose_sampleBelowL`, `Cryptography/Candidates/DiscreteLog.lean`.)
  ```

**Comment-only** (`checks/le-r2.txt`; `commentstrip.py` removes line comments and nested block comments, including `/--`
and `/-!`, and honours string literals):
- Each file at `89a18a82` and at `98cb0e52` is **byte-identical** once comments are removed. The stripped SHA-256s are
  `6538e35f…` (`Draws`), `e577cc16…` (`Words`) and `357556c5…` (`Handler`).
- Three code mutations per file are each caught: a space after the first `:=`, a duplicated code line, and `theorem`
  changed to `lemma`. LE-g44 changes no other path.
- Lines: `Draws` 451 → 460, `Words` 632 → 635, `Handler` 899 → 902. Max width 99, 99 and 100 characters; no tab or
  trailing space.

**The cited construction** (`checks/sources-r2.txt`; `sources-r2.zip` `T44p-bee027f0/`):
`TCSlib/Cryptography/Candidates/DiscreteLog.lean`, namespace `TCSlib.Cryptography.Candidates`, is the same blob at the
tip, `89a18a82` and T44′.
- `sampleBelowL (m k B T : ℕ) (r : List Bool) : Option ℕ` is at line 578.
- `statClose_sampleBelowL` is at line 618:

  ```lean
  theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
      StatClose (fun b : Fin (n * n) → Bool => (sampleBelowL m (Nat.size m) n n (List.ofFn b)).getD 0)
        (fun x : Fin m => (x : ℕ)) ((1 / 2 : ℝ) ^ n) := by
  ```
- `Draws.statClose_draw` applies it with `m = p` (its proof, unchanged, calls
  `Candidates.statClose_sampleBelowL hm hmn`).

**Tags** (`checks/sources-r2.txt`): no source tag is added or removed (`Draws` 5, `Words` 3, `Handler` 5). Every key has
a `## References` entry. Each remaining "Theorem 52.3" (`Draws` 2, `Words` 1, `Handler` 1) sits beside "context". The
PS10 excerpt (`references/pass-shelat-2010-ch2.raw.lines1338-1420.md`, as in round 1) shows Theorem 52.3's
`D_i = Z_q` and the proof's "It is easy to sample the domain D_i".

Is LE-g44 comment-only? Does it attribute the bounded sampler and its bound to the right library construction, keep
PS10 only as context, and correct the three References entries consistently? Does it close G44-02?

### 3. G44-03: the corrected control figures

The paired controls on `Pairing/Assumptions` (round 1's `rule10/asm/`; `checks/g44-03-controls.txt` recounts the raw
logs at `$SP/g44/run/asm/rule10/seal-runs/mods/`):
- **Per variant** (strict, coe): **2 sealed probes** (`ControlS_A`, `ControlS_B`) and **2 unsealed probes**
  (`ControlU_A`, `ControlU_B`), with **25 expected sealed negatives: 12 in A and 13 in B** (B also has
  `PolyExpr.eval`).
- **Across strict and coe:** 4 sealed and 4 unsealed probes and **50** negatives.
- Each sealed negative fails exactly once (the logs count 12 and 13 `error:` lines, 0 `error(`). Every reader passes,
  and every unsealed probe has 0 errors. `ctlcheck`: **ALL_OK True** in strict and in coe.

`pack-r1.md:339–341` said "4 sealed and 4 unsealed probes per variant" and "50 `error:` lines in each of strict and
coe". Both are doubled. Nothing else in round 1's figures changes. Are these figures right?

### 4. T44′: the replay and the seals

Recipe: `briefs/pass-shelat-ch5-8/maintainer/snapshots.md`, job recipe steps 1–5, on a copy of round 1's output
instead of the snapshot. The tools are round 1's (`$SP/g44/tools`), unmodified; the drivers are new
(`replay/tools/run-build-g44b.sh`, `rule10/tools/rule10_g44b.sh`). One Lean process at a time.
- **Copy.** Snapshot #4 rehashed 0/0/0 against its map (`6607620d…`) before the job. Round 1's output
  `$SP/olean-replay-g44` matched its map `ded2f64d…` (1458 entries, no Mathlib) before the copy. `cp -al` gave
  `$SP/olean-replay-g44b`: 1459 files, all hard links, and round 1's 3346 Mathlib symlinks with the NthRootLemmas olean
  `c0a9cff0…`.
- **Plan.** `downorder.py` T44′ against T44 gives 3 changed and 10 downstream modules. `fullorder.py` at T44′ gives
  1427 modules (root `TCSlib` and both `audits/*/Checks`). `stateplan.py plan` runs on a copy of round 1's final state
  (keyed at T44; SHA-256 recorded) and builds **10**, reusing 1417. The queue equals the downstream set: `BBM/Draws`,
  `BBM/Words`, `BBM/Handler`, `BBM/Reduction`, `BBM/Oracles`, `IB/BonehBoyenMachine`, `IB/BonehBoyenSecurity`, the
  facades `IdentityBased` and `AdvancedEncryption`, and root `TCSlib`.
- **Build** (`runner.py` through `scripts/lean_check_tree.sh`, 05:50–05:51 UTC): **10/10 rc 0, 0 `error:`, 0 `error(`,
  0 occurrences of "error"**. There are exactly 2 warnings, both `declaration uses 'sorry'` in `BonehBoyenSecurity` (T2,
  T3), as at T44.
- **Olean comparison** (`replay/checks/rebuilt-linkcount.txt`). The 7 downstream oleans are byte-identical to round 1's
  T44 oleans (`Reduction`, `Oracles`, `BonehBoyenMachine`, `BonehBoyenSecurity`, both facades, root). The 3 changed
  modules' oleans differ, as they must: docstrings and declaration positions.
- **State.** `stateplan update` took 10. `stateplan check` over the 1427-module full closure: **RESULT OK**.
- **No write-through.** All 10 rebuilt oleans have link count 1, and there is no `.ilean`. Snapshot #4 rehashed **0/0/0**
  after the job. Round 1's output still matched `ded2f64d…` after the build.
- **Output map** (`replay/output-map/map.out`, Mathlib excluded): 1458 entries, SHA-256
  **`fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9`**. Against round 1's: 1455 equal and 3 changed
  (`Draws`, `Words`, `Handler`). Against snapshot #4: 4 changed and 5 added, as in round 1.
- **Admissions** (`tipcensus.py`, round 1's record sets plus this job's): T44 **196** and T44′ **196**, identical per
  module. The three changed modules have 0.
- **Axioms** (`replay/axioms/`: `Axioms44.lean`, round 1's probe, unchanged, on the new output): rc 0, 0 errors. The log
  is **byte-identical** to round 1's: T1 and T4 use the standard three; `bb1_sidSecure` reaches `sorryAx` exactly
  through T2 and T3; the 9-owner census has 604 constants and 0 non-standard.
- **Seals.** Round 1's seals are carried forward by **comment-strip identity**: at T44′ every owner's code equals T44's.
  - The three LE-g44 files are byte-identical after comment stripping (§ 2), and every other source is blob-equal.
  - The collector over #346's eight owners, run at T44′, has a probe and a log **byte-identical** to round 1's (log
    SHA-256 `9da792a2…`, the value round 1's seal manifests record), so the request rows cannot have moved.
  - Confirmation: the **canonical coe-A seal** at T44′ on the three changed owners and on `IB/BonehBoyenMachine`
    (`rule10/seal/`):

    | Owner | requests | rc | `error:` | `error(` | install / EOF |
    |---|---:|---:|---:|---:|---|
    | `BBM/Draws` | 1644 | 0 | 0 | 0 | yes / yes |
    | `BBM/Words` | 2242 | 0 | 0 | 0 | yes / yes |
    | `BBM/Handler` | 2275 | 0 | 0 | 0 | yes / yes |
    | `IB/BonehBoyenMachine` | 2311 | 0 | 0 | 0 | yes / yes |

  - `rule10/seal/sealcarry.txt` compares each record with round 1's coe-A record of the same owner. `Draws` was not run
    in round 1, so its record there is the one under `rel/`. Rows, term readers, excluded terms and counts are
    identical. The harness insertions are identical in kind, size and SHA-256. Each probe minus its insertions gives its
    tree's source byte for byte, and the two probes are identical after comment stripping. `BonehBoyenMachine`'s probe
    is byte-identical. **RESULT OK.**
  - Not re-run, because their inputs are unchanged:
    - strict A/B and coe B on these four;
    - all four variants on `Reduction`, `Oracles`, `Assumptions`, `Defs` and `BonehBoyen`;
    - the paired controls;
    - the supplement (Joux, `BonehBoyenSecurity`, both facades);
    - the explicit-unfold scan, whose items are code tokens and so cannot change under a comment-only edit.
- **Lint** (`lint/`). `campaign_style_lint.py TCSlib/Cryptography --check8b` at T44′ gives 92 FAIL / 104 WARN over 524
  files. Its non-INFO lines are identical to round 1's T44 run. The INFO changes are the line counts of the three files:
  `Handler` 902 and `Words` 635 are over the 600 target and under the 1000 cap. `style_lint.py` on the three files: 0
  findings; `sk15`: 0 hits.

Does the evidence bind to T44′ and show no regression? Is comment-strip identity, with the four coe-A seals and the
identical collector, sufficient to carry round 1's seals? Or is a re-run necessary? Missing necessary evidence would be a
major.

### 5. Round 1's passes still hold

T1's file and every #346 file other than the three are blob-equal at T44 and T44′ (`checks/headers-r2.txt`). The three
differ only in comments (§ 2). So the following are unchanged since round 1:
- the proofs and their edge cases;
- the frozen headers and prose of T1–T4 and `bb1_sidSecure`;
- the seven readers and LE-bb1m;
- the 174 public declarations (`rule10/statements/touched-after.tsv` gives round 1's statuses and names: 99 UNCHANGED,
  2 CHANGED, 17 ADDED, 246 in new files);
- the name-clash result.

The grades of BM-F01–BM-F09 and of #340's seven disclosures stand, with item 5 now ledgered (DL-55). Does anything in
LE-g44 or the records reopen a round-1 pass?

### 6. Is anything new undisclosed?

New since round 1:
- LE-g44;
- the records commits after `8f888790`, up to the pin;
- the staging commit: this pack, the resolutions, the three corrections and the round-2 evidence;
- the PR description updates, posted by Seyoon before dispatch.

Is any change, claim or omission among them undisclosed? The known slips are below.

## Merge interaction (maintainer merge conditions, not audit items)

- `$SP/olean-replay-g44b` (map `fca1b6a3…`) is **kept**. It becomes **snapshot #5** if #340 and #346 both merge and the
  final merge commit's Lean equals T44′ (procedure step 3).
- Round 1's output `$SP/olean-replay-g44` no longer matches any landing tree once LE-g44 is on #346. Its map
  `ded2f64d177fc73a55c8f55e0ad1bc4699392c2a53c7cfb45f9152b55ed4abda` was rechecked equal and recorded. The directory was
  then **deleted** at 06:03 UTC (`replay/checks/g44-deleted.txt`). Afterwards `olean-replay-g44b` still matched its map
  and snapshot #4 rehashed 0/0/0.
- `$SP/olean-replay-346c` (#346 alone, round 1's head) is equally stale for #346′ and is not used.
- If #346 merges without #340, a fresh replay of tip × #346′ is needed.

## Known dispositions and slips (not findings)

- **LE-g44 is local at staging.** The commit is signed, and #346's remote branch is still at `89a18a82` when this pack is
  filed. Seyoon or the maintainer pushes `land/pairings-bb1-machine` to `98cb0e52` before dispatch. The dispatch prompt
  pins the commit by hash.
- **The PR descriptions** are not edited by the staging job. Drafts went to Seyoon: #346's adds LE-g44, the new head and
  the round-1 outcome; #340's corrects the *Overlap and reuse* bullet to "disclosed and accepted, DL-55". The live bodies
  are the record. At staging they still equal round 1's `pr340-description.md` and `pr346-description.md`
  (`pr/pr-rest-fields-r2.json`, fetched at 05:58 UTC).
- **Library context, not changed.** `Candidates/DiscreteLog.lean`'s own docstring of `sampleBelowL` cites
  `[PS10, Theorem 52.3, "it is easy to sample the domain D_i"]` for the acceptance-rate remark. It is outside both PRs
  and is left as it is.
- **`draw` keeps a `[PS10, Theorem 52.3]` tag**, marked as context, so that the declaration still points to the source
  remark. The finding allowed keeping it as context.
- **The replay base is round 1's output, not snapshot #4.** It holds T44's oleans, keyed at T44 in round 1's state, so
  the plan rebuilds only the LE-g44 downstream.
- **Signatures.** There is no `ssh-keygen` in the container, and `%G?` prints N (no `allowedSignersFile`).
  `checks/series-r2.txt` verifies the signatures in Python (round 1's `ssh_sig`, unchanged).
- **Sizes.** `Handler.lean` 902 and `Words.lean` 635 lines: over the 600 target and under the 1000 cap, as in round 1
  (BM-F07).

## Evidence files

- **`resolutions-r1.md`** and **`findings-r1.md`**: the round-1 dispositions and findings.
- **`le-g44.diff.txt`**: `git diff 89a18a82..98cb0e52`; 3 files, +22/−7 (SHA-256 `e81b86c8…`).
- **`pr346-r2.diff.txt`**: `git diff 7291f6b2..98cb0e52`. It equals the three-dot `git diff 4f4a7592...98cb0e52` byte for
  byte: 8 files, +2756/−17 (SHA-256 `116a4d09…`). #340's diff is round 1's `pr340.diff.txt`, unchanged.
- **`source-head-r2.json`**: the pins, and for each of the 9 files at T44′ its status, blob, SHA-256, line counts (and at
  T44), widths, and whether it changed since round 1 (only the three).
- **`sources-r2.zip`**: the three LE-g44 files at `98cb0e52` and `89a18a82`; `Candidates/DiscreteLog.lean` at T44′; the
  PS10 §2.8 lines. The source closure is round 1's `sources-r1.zip`; T44′ differs from it only in the three files.
- **`verification-r2.zip`**. `MANIFEST.md` gives each entry's provenance, and `SHA256SUMS` lists every other entry.
  - `checks/`: `series-r2`, `le-r2`, `mergetrees-r2`, `headers-r2`, `sources-r2` and `g44-03-controls`, with their
    scripts (`checks/tools/`). They are generated from git objects; no Lean.
  - `landing/`: the merge-tree record.
  - `replay/`: copy and export, orders, plan, state, the build with every module log, link counts and olean
    comparison, base rehashes and round 1's map rechecks, the output map, admissions, axioms (probe source and log),
    lint, and the drivers and tool list.
  - `rule10/`: the statements, the collector (probe source and log), the four coe-A seal records, probes, run records
    and logs, `seals-coe-A.tsv`, `sealcarry.txt`, and the driver and `sealcarry.py`.
  - `records/`: the ruling rows of the plan, ledger rows DL-55/DL-56, the Stage 2 scope, and the three corrections as
    filed.
  - `pr/`: the REST fields of #340 and #346 read at staging.
- **`SHA256SUMS-r2`**: the round-2 files of this gate directory.
- **Round 1:** `outbox/gates/44-pairing-fills-gate/` on the exchange at `30ef1257a56873489b599007782046b7dedeb7fc`, with
  records `8f888790b7e40f9e0529967e29a05a72c5ee8ba3`. `pack-r1.md` here is its pack, and its evidence is
  `verification-r1.zip`.

## Findings delivery

Return `gate44-pairing-fills-r2-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP.
Use round 1's table and severities:
- say for each round-1 finding whether it is closed;
- say whether round 1's passes still hold;
- name anything new;
- report the audited heads, T44′ and the counts by severity.

The gate closes at zero blockers and zero majors.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope violation.
- **major:** any of the following:
  - a changed frozen statement;
  - a forbidden read in a touched declaration not covered by the rulings;
  - an undisclosed copied private lemma, or an undisclosed re-proof of a public one, outside the ledger rows and rulings
    in force;
  - a fabricated source tag;
  - necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, proof sketch or citation.
- **note:** anything else.

## ===== resolutions-r1.md (this pack) =====

# Gate 44 · resolutions, round 1 · HOLD → ruling, landing edit, pack correction

Codex's verdict is **HOLD**: 0 blockers, 1 major, 1 minor, 1 note.
- **Findings:** `findings-r1.md` (verbatim, filed by the maintainer; the evidence ZIP it mentions was not received).
- **Audited:** #340 at `916afc25c21f5e52b4b01958186ad55d2f615fd1` and #346 at `89a18a8225be1b76166af12a15179da291747783`;
  records `8f888790`; exchange `30ef1257`; joint tree T44 `33681cb8`.

Codex found **no mathematical gap**. Its confirmations are listed below.
- **Proofs.** T1 and T4 establish their frozen statements, edge cases included.
- **Integrity.** The frozen statements and the seven readers are intact, and LE-bb1m is proof- and doc-only.
- **Rule 10.** 24/24 joint-owner and 16/16 supplement seals pass, and request-set identity justifies reusing the seals of
  the three skipped owners.
- **Replay and axioms.** 16/16 rc 0, admissions 198 → 196, the standard axioms.
- **Grades.** BM-F01 to BM-F09 are all agreed. Six of #340's seven overlap disclosures are agreed; item 5 is G44-01.

| Finding | Grade | Resolution | Evidence and pointer |
|---|---|---|---|
| G44-01 | **major** | **Accepted and ledgered** (Seyoon, 2026-11-17, ruling G44-01). The two disclosed re-derivations are retained, and the debt is repaid in cleanup Stage 2. **DL-55:** T1's inline verdict identity (`Pairing/Assumptions.lean:199`) re-derives `TrapdoorPredictor.decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean:144`). Stage 2 promotes that lemma to a shared low-level home, then re-points `TrapdoorPredictor` and T1 (proof-only). **DL-56:** #346's `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` (`BonehBoyenMachine/Words.lean:261–271`) re-prove `Games.polyTimeComputable_rU`/`_rZ`/`_rW`/`_rS` (`Games/Efficiency.lean:538–550`). Stage 2 re-points the four, with a reader if the recorded obstruction needs one (proof-only). Both reports' "No duplicated proved material; nothing for the duplication ledger." lines keep their text, with a dated correction under each. The bb1-machine review's duplication paragraph carries a matching note. No code change. | `briefs/pass-shelat-ch5-8/duplication-ledger.md` rows DL-55, DL-56 and `cleanup-stages.md` § Stage 2 (records `4f4a7592`). The plan's ruling row of 2026-11-17. Corrections: `fills/pair-bdh/inhouse-r1/REPORT.md` (under line 99), `fills/bb1-machine/inhouse-r1/REPORT.md` (under line 260), and `fills/bb1-machine/final-r1/review.md` (§ Duplication and reuse). |
| G44-02 | minor | **LE-g44** on #346, docstrings only, commit `98cb0e521a94e94c304c78348fb5d3033435a3ed` on `89a18a82`. `Draws.lean`'s module docstring and `draw`'s docstring now attribute the bounded rejection sampler and its bound to the library's existing construction: `Candidates.sampleBelowL` and `Candidates.statClose_sampleBelowL` (`Cryptography/Candidates/DiscreteLog.lean:578`, `:618`). For `0 < m < 2^n`, the sampler on `n · n` uniform coins with the fallback `0` is within `(1/2)^n` of uniform below `m`. `[PS10, Theorem 52.3]` (§2.8) is kept as context only: its proof remarks that the domain `Z_q` is easy to sample. The `## References` entries of `Draws.lean`, `Words.lean` and `Handler.lean` are corrected consistently. Each file is byte-identical to the parent once comments are stripped. | `pack-r2.md` § 2. `verification-r2.zip`: `checks/le-r2.txt` (comment-strip identity with controls), `checks/sources-r2.txt`, and `le-g44.diff.txt`. Replay T44′ (§ 4). |
| G44-03 | note | **Corrected in the round-2 pack** (no replay or control repair). Round 1's `pack-r1.md:339–341` doubled the paired-control figures on `Assumptions`. The actual figures, per variant (strict, coe), are **2 sealed and 2 unsealed probes**, with **25 expected sealed negatives (12 in A, 13 in B)**. Across strict and coe together that is 4 sealed and 4 unsealed probes and **50** negatives. Every negative fails exactly once, every reader passes, and every unsealed probe has 0 errors: ALL_OK in both variants. The round-1 pack stays as filed. | Recount from round 1's raw control logs: `verification-r2.zip` `checks/g44-03-controls.txt`. |

**Checks for the new head and T44′:**
- LE-g44 changes docstrings and comments only.
  - With comments stripped, each of the three files equals its parent byte for byte.
  - Three code mutations per file are each caught.
  - No other path changes.
- T44′ = records tip `4f4a7592` × #340 `916afc25` × (#346 + LE-g44) = tree
  `bee027f0903d531b3a43511cea16bfa123210291` in every merge order.
  - It differs from T44 in exactly the three LE-g44 files.
- Replay on a `cp -al` copy of round 1's output (`$SP/olean-replay-g44b`): the three files and their downstream.
  - Build: 10/10 rc 0, 0 errors; state check OK over 1427 modules; every rebuilt olean has link count 1.
  - Snapshot #4 verifies 0/0/0.
  - The 7 downstream oleans are byte-identical to T44's.
  - Admissions are 196, unchanged, and the axioms log is identical.
- Seals carried forward by comment-strip identity, confirmed by canonical coe-A on `Draws`, `Words`, `Handler` and
  `BonehBoyenMachine`.
  - Each is rc 0 with 0 errors.
  - Each request set is row-identical to round 1's.
- Lint has no new FAIL or WARN.

Then Gate 44 round 2 (Codex) at #346 `98cb0e52` with #340 `916afc25`.

## ===== findings-r1.md (this pack) =====

<!-- Filed by the maintainer on 2026-11-17 from the auditor's chat reply, pasted by Seyoon. The text below is verbatim.
The evidence ZIP it mentions (gate44-pairing-fills-evidence.zip) was not uploaded; only this Markdown was received. -->

# Gate 44 pairing fills — round 1 findings

**Verdict: HOLD. Open findings: 0 blockers, 1 major, 1 minor, 1 note.**

The delivered proofs establish the frozen T1 and T4 statements. The hold concerns the required acceptance of disclosed duplication.

| Audited item | Pin |
|---|---|
| Exchange | `30ef1257a56873489b599007782046b7dedeb7fc` |
| Campaign records | `8f888790b7e40f9e0529967e29a05a72c5ee8ba3` |
| #340 / merge base | `916afc25c21f5e52b4b01958186ad55d2f615fd1` / `9e7a96481785d6cac4dea3b2e990c49ac278b060` |
| #346 / merge base | `89a18a8225be1b76166af12a15179da291747783` / `7291f6b237fec75add1549c0992c174442180488` |
| Joint tree T44 | `33681cb8ed893a897ca2028d5ada70ca29237978` |

## Findings

Lean paths below are under `TCSlib/Cryptography/`.

| ID | Severity | PR · location | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G44-01 | **Major** | #340, `Pairing/Assumptions.lean:199`; #346, `IdentityBased/BonehBoyenMachine/Words.lean:261` and neighboring reader proofs | Disclosed exact re-derivations are classified as “no duplicated proved material; nothing for the duplication ledger.” T1’s inline verdict identity is precisely public `TrapdoorPredictor.decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean:144`), specialized to the solver-success decision bit. The checkpoint’s `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` also re-prove the polynomial-time facts for identical public `InteractiveHandler` projection functions (`Games/Efficiency.lean:538`, `:542`, `:546`, `:550`). Both families are disclosed, but no explicit human acceptance and scheduled repayment is recorded in the audited material or pinned duplication ledger. Policy §1 requires that acceptance, including for mechanically forced copies. | Reuse shared facts, promoting missing generic readers where necessary; or record Seyoon’s explicit acceptance, the shared home and repayment point. Correct both reports’ “nothing for the ledger” dispositions. |
| G44-02 | **Minor** | #346, `BonehBoyenMachine/Draws.lean:58`, `:130`; References entries in `Words.lean:60` and `Handler.lean:62` | `[PS10, Theorem 52.3]` is an inaccurate locator for bounded rejection sampling. That theorem concerns the discrete-log collection of one-way functions; its proof merely remarks that the domain is easy to sample. It does not specify this sampler, fixed coin budget, fallback or statistical bound. The actual formal justification is `Candidates.statClose_sampleBelowL`. This is a genuine source with an inaccurate citation, rather than a fabricated-tag major. | Attribute the bounded sampler to the existing library construction and bound. Retain PS10 §2.8/Theorem 52.3 only as context, and correct the three References entries consistently. |
| G44-03 | **Note** | `pack-r1.md:339`, Assumptions paired-control figures | The prose doubles the totals. Each variant has **2 sealed and 2 unsealed probes**, with **25** expected negative errors: 12 in A and 13 in B. Across strict and coe together: 4 sealed, 4 unsealed and 50 negative errors. The raw logs and plans verify these actual counts, with every reader passing. | Correct “per variant” and “50 … in each.” No replay or control repair is needed. |

The PS10 source supports G44-02’s distinction between its discrete-log theorem and the bounded sampler. [cs.cornell.edu](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf?utm_source=chatgpt.com)

G44-01 is an acceptance/ledger requirement. The overlaps were disclosed; it is **not** an undisclosed-copy accusation.

## Proof and scope checks

| Question | Result |
|---|---|
| **1 — T1 correctness** | **Pass.** `exists_bdhDistinguisher` constructs a total polynomial-time raw function through `NUPPT.ofPolyTime`, retaining the solver’s coins and advice. On the real tuple law, `coinsCongr` and `expect_sample_equiv` preserve success probability and the unused target sample disappears. On the random law, exchanging independent target/coin samples and encoding injectivity give the inverse-order bound, including outputs outside the encoding range. `accept_bdhGame_le` is pointwise in the security parameter; the bad-order charge is exactly the stated hypothesis. The final negligibility argument adds no assumption. |
| **1 — T4 correctness** | **Pass.** The handler uses total polynomial-time string operations. Negation reduces before subtracting from the modulus; differences and inverses agree with `ZMod`, including inverse zero. Membership precedes message decoding. The per-call identity covers all three oracles and every simulator state. At most one tape entry is consumed per oracle call, so the budget suffices. The sampler is exactly G40-03’s; encoding injectivity supplies its strict modulus bound on every generated group. Machines and error function are chosen before the universally quantified bits and security parameter. |
| **1 — edge cases and sufficiency** | **Pass.** Parameter zero, zero budget, empty coins/advice, absent initialization/challenge, refused target-key queries, repetitions, invalid messages and identity collisions are covered. T4 requires no identity-injectivity/order-growth hypothesis: both simulations use the same zero-inverse convention. Orders zero and one and invalid mathematical group objects are excluded by `BilinearGroup`’s fields; malformed machine strings still receive total polynomial-time behavior. `bb1_sidSecure` is unchanged and reaches `sorryAx` exactly through T2 and T3. T1 is not used by that consumer. |
| **2 — frozen declarations** | **Pass.** Independently reconstructed T44 from the pinned trees; both PR diffs match the pack. T1/T4 headers and statement prose are unchanged. Restoring permitted regions restores the base files. All six T1 and ten T4 mutation controls reject their mutations. The checkpoint inserts only its four imports and Contents section. Public declarations: 101 → 275, exactly 174 additions, with no other frozen declaration changed or removed. |
| **3 — seven readers** | **Pass.** Independent reconstruction is byte-exact: `Defs` +43/−0, `BonehBoyen` +37/−0 at the approved positions. All nine controls reject their mutations. These are precisely the three `oracleImpl_*_onSpec` readers and four approved BB1 encoding/message-space readers, with approved proofs and no added attribute. The casts’ `rfl` witnesses read `Defs`’ own `sidSpec`; consumers use published theorems. |
| **4 — LE-bb1m** | **Pass.** Direct parent/head comparison confirms only deletion of unused `hpp` and reordering of the formula docstring. No statement changes. |
| **5 — duplication** | G44-01 and the grading tables below. No additional undisclosed duplicate was identified. The checkpoint overlaps were reviewed beyond the full-name clash check. |
| **6 — Rule 10** | **Pass.** Recounted **24/24** joint-owner and **16/16** supplement seals: source/probe hashes, conservative request sets reconstructed from collector catalogs, exact source recovery after removing harness insertions, install/EOF coverage, rc 0 and no errors. Strict/coe A/B exclusions match the rulings. Assumptions controls pass at the corrected counts; supplement controls give 24 expected negatives per variant, with all readers/unsealed controls passing. The three skipped owners have **12** row-, source- and probe-identical records against phase 2; its **32/32** earlier seals also recount cleanly. Those owners do not import changed Assumptions, so unchanged inputs justify reuse. The explicit scan has 1,016 items and zero foreign reads; source inspection agrees. |
| **7 — sources** | **Pass apart from G44-02.** BB04 §4.2/Theorem 4.1 and algorithm B are correct sources. The theorem is on printed p. 6 and its proof on pp. 7–8, so the locators are compatible. T1’s independent folklore attribution is accurate under Q10. PS10 Algorithm 43.2 and Definition 181.1 are apt for Euclid and statistical closeness. Inherited missing SOK00/BF01 entries remain outside these fills. |
| **8 — documentation** | **Pass apart from G44-02.** New public docstrings state their formulas; sketches describe the delivered proofs. The sole 15-line sketch omission is pre-existing frozen `bb1SimChal_fresh`. “Handler theorem T1” explicitly names `Games.exists_handlerMachine`, distinguishing it from pairing T1; consistently spelling out “Games” would improve readability. |
| **9 — replay and axioms** | **Pass on supplied evidence.** Independently reconstructed the 16-module downstream set and 1,427-module root/audit closure. All 16 build logs and source bindings recount cleanly: rc 0, no errors, exactly the two T2/T3 admission warnings. Census: **198 → 196**, exactly T1 and T4 removed. Both targets have the standard three axioms and no sorried dependency; the owner census has 604 constants and no nonstandard axioms. State, output-map and snapshot-preservation records are consistent. |
| **10 — disclosures** | G44-03 is an additional pack discrepancy. Other recorded staging/provenance slips do not alter the audited code or conclusions. The shared signing key establishes account-session provenance, not individual authorship. |

The BB04 page locators and the PS10 Euclid/statistical-closeness locators were checked against the primary texts. [crypto.stanford.edu](https://crypto.stanford.edu/~xb/eurocrypt04b/bbibe.pdf?utm_source=chatgpt.com)

The principal bounds checked are

\[
\operatorname{accept}(G.\mathrm{bdhGame}\ A\ \kappa)
\le G.\mathrm{dbdhAdv}\ D\ \kappa+2^{-\kappa}+\delta(\kappa),
\]

\[
q(\kappa)2^{-n}\le(q(\kappa)+1)2^{-\kappa}=\sigma(\kappa),
\qquad n=\kappa+w_G(\kappa)+1.
\]

## Grades: BM-F01–BM-F09

These dispositions do not add to the open-finding counts.

| Finding | Grade / disposition |
|---|---|
| BM-F01 | Agree: note, **closed** by removal of the unused proof. |
| BM-F02 | Agree: minor, **closed** by corrected argument order and explicit security parameter. |
| BM-F03 | Agree: evidence note, **closed**. Independently recounted Oracles controls: 14 negative and 14 reader rows per variant, all as expected. |
| BM-F04 | Agree: note, superseded by landing-head seals and unchanged-input comparisons. |
| BM-F05 | Agree: evidence nits; source/log/hash checks resolve the substantive questions. G44-03 is separate. |
| BM-F06 | Agree: inherited documentation note, outside permitted edits. |
| BM-F07 | Agree: size note; the files exceed the target but remain below the cap. |
| BM-F08 | Agree: disclosed promotion request. The private range-type lemmas derive from published readers without re-proving an existing public IBE theorem. |
| BM-F09 | Agree: suitable machine-specific public glue, with its formula and sketch. |

## Grades: #340’s seven overlap disclosures

| Item | Grade / disposition |
|---|---|
| 1 — raw machine versus `NUPPT.wrap` | Agree. Composition of verified construction layers; the alternative’s bookkeeping does not make this an additional copied theorem. |
| 2 — equality test | Agree. `polyTimeComputable_pairEq` is reused. |
| 3 — projections | Agree. Fixed compositions of published projections; the iterated-first-projection theorem does not supply the required second-projection contract. |
| 4 — target probability | Agree. Tuple-specific application of published probability/injectivity facts; the list-membership bound is a near-alternative. |
| 5 — verdict identity | **Reject “no duplicated proved material / no ledger”: G44-01.** The exact public identity is re-derived inline. Disclosure does not establish acceptance of retained debt. |
| 6 — bad-order bound | Agree as disclosed pattern overlap. The ElGamal safe-prime/index proof is not copied as an interchangeable theorem. |
| 7 — advantage inequality | Agree. Direct absolute-value API use; no matching public Games lemma was identified. |

The checkpoint’s identical round-input projections and polynomial-time facts have the same acceptance gap. Its API obstruction is real, but the required acceptance/repayment record is absent. Other disclosed specializations, casts, encoding-contract applications and simulator comparisons have different contracts or apply existing facts.

## Verification and limits

All **14/14** outer and **549/549** verification-archive checksums pass, with an exact file set. All **186** source-manifest entries pass; **181** Lean source copies bind to pinned git blobs. All **43** bundle sections match their separate copies. The two additionally consulted review archives verify **962/962** and **255/255** inner files and their pinned outer hashes.

The ZIP contains the independent checks, results, mutation-control reruns and pinned duplication ledger. **I did not run a fresh Lean compilation**; compilation/axiom conclusions use the hash-bound supplied replay and probes, independently recounted and checked against the inspected sources.

Gate 40, the T2/T3 fill and #351/#352 are not re-audited. Merge order and snapshot adoption remain maintainer conditions.

**Notation:** `A`: adversary/solver; `D`: reduction distinguisher; `G`: bilinear generator; `κ`: security parameter; `q(κ)`: query budget; `w_G(κ)`: source-group encoding width; `n`: sampler width defined above; `δ(κ)`: bad-order bound; `σ(κ)`: simulation-error bound. T1/T4 and BM-F01–BM-F09 retain the campaign’s labels.

## ===== verification-r2.zip:records/corrections/corrections.diff (this pack) =====

diff --git a/briefs/pairings/fills/bb1-machine/final-r1/review.md b/briefs/pairings/fills/bb1-machine/final-r1/review.md
index ffb8de0b7..50c67b73f 100644
--- a/briefs/pairings/fills/bb1-machine/final-r1/review.md
+++ b/briefs/pairings/fills/bb1-machine/final-r1/review.md
@@ -106,6 +106,7 @@
     - `ofFn_decAnswer_some` is `decAnswer_some` plus Mathlib `List.ofFn_cons`, as disclosed;
     - `sidSpec_rng_one'`/`_two'` have no published IBE counterpart; the promotion request is recorded and not asked for this PR.
   - The new public `ofFn_padFin` (`ComposeSecurity/Machines.lean:244`, on the tip) maps to `padTo` and is not a restatement.
+  - **Correction (2026-11-17, Gate 44 G44-01).** This review checked the worker's delta only. It took the checkpoint helpers' overlap dispositions from the in-house REPORT, including its line "No duplicated proved material; nothing for the duplication ledger" (`inhouse-r1/REPORT.md:260`), without regrading them. That line is wrong for the checkpoint's `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` (`Words.lean:261–271`), which re-prove `Games.polyTimeComputable_rU`/`_rZ`/`_rW`/`_rS` (`Games/Efficiency.lean:538–550`). They are disclosed, but no acceptance was recorded. Seyoon accepted them on 2026-11-17: ledger row **DL-56**, repaid in cleanup Stage 2. The REPORT carries a dated correction under the line, and the verdict above is unchanged. See `gates/44-pairing-fills/resolutions-r1.md`.
 - **Rule 10, by source reading** (my `unfold_scan.py` over `Oracles.lean` and T4's body):
   - It finds 184 theorem selectors and 0 foreign TCSlib or core/Mathlib definitions.
   - The other rows are local hypotheses, the `@[simps]` readers `bb1Scheme_{pp,sk,ct}Len`, `abs_sub_comm` (via `to_additive`), or tokenizer artefacts.
diff --git a/briefs/pairings/fills/bb1-machine/inhouse-r1/REPORT.md b/briefs/pairings/fills/bb1-machine/inhouse-r1/REPORT.md
index 565b1b79c..9234c597c 100644
--- a/briefs/pairings/fills/bb1-machine/inhouse-r1/REPORT.md
+++ b/briefs/pairings/fills/bb1-machine/inhouse-r1/REPORT.md
@@ -259,6 +259,16 @@ Disclosed overlaps of definition or pattern, and near-alternatives:
 
 No duplicated proved material; nothing for the duplication ledger.
 
+> **Correction (2026-11-17, Gate 44 G44-01).** The line above is kept as filed, but its disposition is wrong for
+> disclosure 1. `poly_rU`, `poly_rZ`, `poly_rW` and `poly_rS` (`BonehBoyenMachine/Words.lean:261–271`) re-prove the
+> polynomial-time facts of the public `Games.polyTimeComputable_rU`, `_rZ`, `_rW`, `_rS` (`Games/Efficiency.lean:538–550`):
+> `BB1Machine.rU`, …, `rS` have the bodies of the `InteractiveHandler` projections, and the four proofs are the same
+> compositions. Disclosure 1 records the API obstruction (no published `_eq`
+> readers for those projections under Rule 10), but not an acceptance. Seyoon accepted the debt on 2026-11-17:
+> it is ledger row **DL-56** (`briefs/pass-shelat-ch5-8/duplication-ledger.md`), repaid in cleanup Stage 2
+> (`cleanup-stages.md`): re-point the four to the `Games/Efficiency` facts, adding a reader there if the obstruction
+> needs one (proof-only). Resolution: `briefs/pairings/gates/44-pairing-fills/resolutions-r1.md`.
+
 ## Limits
 
 - T4 is unproved pending the scope request; see above.
diff --git a/briefs/pairings/fills/pair-bdh/inhouse-r1/REPORT.md b/briefs/pairings/fills/pair-bdh/inhouse-r1/REPORT.md
index b2c35be81..b7d6f85e9 100644
--- a/briefs/pairings/fills/pair-bdh/inhouse-r1/REPORT.md
+++ b/briefs/pairings/fills/pair-bdh/inhouse-r1/REPORT.md
@@ -98,6 +98,15 @@ Disclosed overlaps of pattern or near-alternatives:
 
 No duplicated proved material; nothing for the duplication ledger.
 
+> **Correction (2026-11-17, Gate 44 G44-01).** The line above is kept as filed, but its disposition is wrong for
+> disclosure 5. The inline verdict identity (`Pairing/Assumptions.lean:199` at `916afc25`, `simp only [List.cons.injEq,
+> and_true, decide_eq_true_eq]`) re-derives the public `TrapdoorPredictor.decide_singleton_eq_true`
+> (`Encryption/PublicKey/TrapdoorPredictor.lean:144`, `decide ([b] = [true]) = b`), specialised to the solver-success
+> bit. Disclosure did not record acceptance. Seyoon accepted the debt on 2026-11-17: it is ledger row **DL-55**
+> (`briefs/pass-shelat-ch5-8/duplication-ledger.md`), repaid in cleanup Stage 2 (`cleanup-stages.md`): promote
+> `decide_singleton_eq_true` to a shared low-level home importable by both layers, then re-point `TrapdoorPredictor` and
+> T1's proof (proof-only). Resolution: `briefs/pairings/gates/44-pairing-fills/resolutions-r1.md`.
+
 ## Limits
 
 - Seals cover the changed owner only (as instructed). The downstream owners' sources are unchanged and their oleans

## ===== verification-r2.zip:records/decision-log-pairings-g44.md (this pack) =====

# Decision-log extract: PairingCryptographyPlan.md at the records pin 4f4a7592 (the Gate 44 rows of 2026-11-17)

line 413: | 2026-11-16 | **Rulings (Seyoon):** (1) **T4 scope request approved, minimal form**: the 7 readers (`oracleImpl_{zero,one,two}_onSpec` in `IdentityBased/Defs.lean`; `ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK`, `bb1Scheme_msgSpace_iff`, `ofFn_bb1SimCt` in `BonehBoyen.lean`) land **in the T4 PR** as pure insertions with `rfl`/one-line proofs and formula docstrings, as with sc-yao's SY-3 readers. #331 is unchanged; Gate 44 checks they are insertions only. T4 resumes on the next free olean tree. (2) **T2/T3 design: a shared relational simulation lemma in `Games`** (two state types related by an invariant), public and statement-gated with the `bb1-sim` fill; it is preferred to a combined state local to the fill. | T4 resumes; bb1-sim design fixed |
line 416: | 2026-11-16 | **`bb1-machine` issued-r1 staged for external Claude** (lead plus up to 1 sub-agent): records `briefs/pairings/fills/bb1-machine/issued-r1/`; exchange `78d89c5c` on `747b61e7` (adds only `outbox/fills/bb1-machine/`, 70 files; signed; SHA256SUMS verify; pushed). Base `7c0a55e0` (the pushed checkpoint). The brief: the 7 approved readers verbatim as pure insertions (Defs 3, BonehBoyen 4; the 13-reader variant excluded); move `expect_bb1SimImpl`/`abs_inner_le` into a helper; T4's body and sketch only; full evidence (seals A/B strict and coe on every changed owner including Defs and BonehBoyen, controls with reader rows, decls2, frozen and reader-insertion checks, axioms, lint, name clash); delivery to `inbox/fills/bb1-machine/` only. Then the maintainer review, the T4 PR stacked on #331, and Gate 44. | T4 ready to dispatch |
line 419: | 2026-11-16 | **#331 merged** (`22e3f809`): the pairing statements are on the records branch. **#340 (T1) retargeted** to `cryptography/pass-shelat-ch2-4`; its diff is now `Pairing/Assumptions.lean` only (+227/−8), and it merges cleanly. #340 and the T4 PR go to Gate 44 together once T4 is delivered. | #331 merged; #340 retargeted |
line 422: | 2026-11-16 | **T4 delivery review, phase 1: provisional ACCEPT WITH LANDING EDITS** (`fills/bb1-machine/final-r1/review.md`; zip `8157bdfc`). Final delivery `f14ac810`, worker head `c90273fa` (3 unsigned commits on `7c0a55e0`). T4 is proved. The seven readers are verbatim pure insertions (pinned hashes match; 9/9 controls fail as required). T4's header and prose are byte-identical. decls2 +8 / 0 / 0; admissions 57 → 56. No undisclosed duplicate. The worker evidence recounts clean: sweep 189/189, seals 32/32 with 0 errors, 314 controls each failing once, axioms standard, `bb1_sidSecure` reaching only T2/T3. It merges cleanly with the tip, #340 and #341. Findings: 1 minor (BM-F02, docstring argument order) and 8 info. LE-bb1m (`Oracles.lean` only, +2/−8) fixes BM-F01/F02. Phase 2 (Lean) runs on the first rebased tree, followed by the T4 PR and Gate 44 with #340. **bb1-sim statement job staged** (`fills/bb1-sim/issued-stmt-r1/`; exchange `a6a21775` on `48c7a7b4`, pushed; base `bdcadd85`). It covers `stmt/games-relational`, `stmt/pairing-group-helpers` and the reader probe on T4's head. Note: the identity-injectivity helper is stated for naturals below the order (`natCast_inj_of_lt`), because `bitsToNat` is not upstream of `Group.lean`. | T4 phase 1; bb1-sim staged |
line 423: | 2026-11-16 | **Draft PR #346 (T4, `bb1-machine`) opened** at `89a18a82` (branch `land/pairings-bb1-machine`, pushed). It has 7 signed commits on the tip: 3 checkpoints, the worker's 3, and LE-bb1m (`Oracles.lean` +2/−8, BM-F01/F02). The diff against the tip is the 8 T4 files. Phase 2 (Lean) runs on the first rebased tree, then Gate 44 with #340. | #346 opened |
line 425: | 2026-11-16 | **#340 (T1) integration condition met** (cross-build tip × #341 × #340 passes; T1 standard; `Assumptions` re-sealed coe A/B with 0 errors). It waits only on Gate 44, with #346. | #340 waits on Gate 44 |
line 436: | 2026-11-17 | **#346 (T4) phase 2 passed; final verdict ACCEPT WITH LANDING EDITS** (LE-bb1m already #346's 7th commit `89a18a82`; `fills/bb1-machine/final-r1/review.md`, `phase2/`, zip `53a47675…`). Final replay 346c on snapshot #4 (prospective tree `2ec72515`): 12/12 rc 0, state 1427 OK, admissions −1 (T4), standard axioms, `bb1_sidSecure` reaches exactly T2 and T3; seal inputs unchanged since the full snapshot-#2 run (32/32 seals 0 errors, controls ALL_OK incl. the `Oracles` probe BM-F03), coe-A reconfirmed 8/8. Cross-build with #340 on #2 (`b90b966b`): 13/13 rc 0, admissions −2. Replay kept at `$SP/olean-replay-346c` (adoptable only if #346 merges alone). **Next: Gate 44 (#340 + #346).** | #346 P2 |
line 439: | 2026-11-17 | **Gate 44 round 1 staged (Codex)** for #340 (T1) + #346 (T4): records `997aac33` + `a6a3c9b2` (`gates/44-pairing-fills/`), exchange `30ef1257`, records pin `8f888790`. Joint replay T44 `33681cb8` (Lean = `c7be1301`) on snapshot #4: 16/16 rc 0, admissions −2 (T1, T4), standard axioms, `bb1_sidSecure` reaches exactly T2/T3; seals on `Assumptions` and #346's 5 downstream owners 0 errors, controls ALL_OK, 0 foreign unfolds; **supplement** re-seal of the unchanged Gate 40 owners downstream (Joux, `BonehBoyenSecurity`, both facades) 16/16 0 errors, controls ALL_OK. #340 retitled and both PR bodies updated before staging. `$SP/olean-replay-g44` (map `ded2f64d…`) becomes snapshot #5 if both merge with Lean = T44. Ready to dispatch. | G44 staged |
line 440: | 2026-11-17 | **Gate 44 round 1 dispatched (Seyoon)** to Codex cloud, pinned to exchange `30ef1257` and records `8f888790`. Findings return in chat as `gate44-pairing-fills-findings.md`. | G44 out |
line 445: | 2026-11-17 | **Gate 44 round 1 (Codex): HOLD** — 0 blockers, 1 major, 1 minor, 1 note (`gates/44-pairing-fills/findings-r1.md`; the evidence ZIP was not received). T1 and T4 proofs pass every correctness, frozen-scope, reader, Rule 10, replay and axiom check. **G44-01 (major):** disclosed exact re-derivations lack Seyoon's recorded acceptance and repayment — T1's inline verdict identity = `TrapdoorPredictor.decide_singleton_eq_true`; #346's `poly_rU/rZ/rW/rS` = the `InteractiveHandler` projection facts in `Games/Efficiency.lean:538–550`. **G44-02 (minor):** `[PS10, Theorem 52.3]` mis-locates the bounded sampler (`Draws.lean:58`, `:130`; References in `Words.lean`, `Handler.lean`); the justification is `Candidates.statClose_sampleBelowL`. **G44-03 (note):** pack control counts doubled. | G44 r1 HOLD |
line 446: | 2026-11-17 | **Ruling G44-01 (Seyoon): accept, repay in cleanup Stage 2.** Ledger rows **DL-55** (T1 inline identity vs `TrapdoorPredictor.decide_singleton_eq_true`; promote to a shared home and re-point) and **DL-56** (#346 `poly_r*` vs `Games/Efficiency` `polyTimeComputable_r*`; re-point) added to Stage 2. G44-02 is fixed by a docstring landing edit on #346 (LE-g44); G44-03 in the resolutions. Round 2 follows. | G44-01 ruled |

## ===== verification-r2.zip:records/ledger-DL-55-56.md (this pack) =====

# duplication-ledger.md at 4f4a7592: the table header and rows DL-55, DL-56

line 5: | ID | New declaration (where) | Existing copy (where) | Status | Resolution |
line 82: | DL-55 | T1 `BilinearGen.bdhAssumption_of_dbdhAssumption`'s inline verdict identity (`decide ([b] = [true]) = b`, specialised to the solver-success bit; #340, `Pairing/Assumptions.lean:199`; Gate 44 G44-01) | `TrapdoorPredictor.decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean:144`), in the public-key layer, which the pairing closure does not import | Accepted (Seyoon, 2026-11-17, Gate 44 G44-01) | **Cleanup Stage 2:** promote `decide_singleton_eq_true` to a shared low-level home importable by both layers, re-point `TrapdoorPredictor` and T1's proof (proof-only). |
line 83: | DL-56 | `poly_rU`, `poly_rZ`, `poly_rW`, `poly_rS` (#346, `IdentityBased/BonehBoyenMachine/Words.lean:261` and neighbours; disclosed with an API obstruction; Gate 44 G44-01) | `Games.polyTimeComputable_rU`, `_rZ`, `_rW`, `_rS` for the same `InteractiveHandler` projections (`Games/Efficiency.lean:538–550`) | Accepted (Seyoon, 2026-11-17, Gate 44 G44-01) | **Cleanup Stage 2:** re-point the four to the `Games/Efficiency` facts, adding a reader there if the recorded obstruction needs one (proof-only). |

## ===== verification-r2.zip:records/cleanup-stage2.md (this pack) =====

# cleanup-stages.md at 4f4a7592: § Stage 2

## Stage 2: re-point and prune (proof-only)
- Re-point every ledgered copy to its promoted form (DL-35, DL-38 to DL-49, DL-51, DL-52). This includes the
  `OTAnswerWords` pair against #324's `HybridProtocol.length_answers*`, and the ETT averaging-bound copy against the bb1-sim
  promotion in `Games/Probability`.
- Gate 44 G44-01 (Seyoon, 2026-11-17): **DL-55** (promote `decide_singleton_eq_true` to a shared low-level home; re-point
  `TrapdoorPredictor` and pairing T1) and **DL-56** (re-point #346's `poly_rU/rZ/rW/rS` to `Games/Efficiency`'s
  `polyTimeComputable_r*`, with a reader if needed).
- Delete the dead private copies and the public host lemmas left unused by DW-5.
- Clear DW-9's 26 seal failures and `Uniform.lean`'s 4 inherited failures (SY-F07) through readers.
- Sweep in small lint and doc nits, such as the `BobIO` unnecessary `simpa`.
- **Gate:** a proof audit, plus the full Rule 10 seal sweep over every touched owner. Target: every Pass–shelat ledger row
  closed, and no seal failure in any touched file.

## ===== verification-r2.zip:MANIFEST.md (this pack) =====

# Gate 44 round 2 · verification archive

`SHA256SUMS` lists every other entry. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`,
and the job directory is `$SP/g44r2`. Pins:
- T44′ = `bee027f0903d531b3a43511cea16bfa123210291`, from the records tip `4f4a7592a54cf82fa04f96b83645d7936672614c`,
  #340 `916afc25c21f5e52b4b01958186ad55d2f615fd1` and #346 + LE-g44 `98cb0e521a94e94c304c78348fb5d3033435a3ed`;
- round 1's T44 = `33681cb8ed893a897ca2028d5ada70ca29237978`.

| Path | What | Provenance |
|---|---|---|
| `checks/series-r2.txt` | records pin, LE-g44 commit and signature (with tamper control), #346's new diff | `checks/tools/chk44r2.py`, git objects only |
| `checks/le-r2.txt` | LE-g44 comment-only: stripped texts byte-identical, three mutation controls per file, widths | same |
| `checks/mergetrees-r2.txt` | T44′ in three merge orders; T44′ vs tip (9 files, blob-equal to the heads); T44 vs T44′ (3 files) | same |
| `checks/headers-r2.txt` | blob equality T44 = T44′ for T1/T2/T3/T4/consumer files and the cited library file | same |
| `checks/sources-r2.txt` | tags of the three files, References keys, the Theorem 52.3 context check, the cited declarations | same |
| `checks/T44p.diff.txt` | `git diff` records tip → T44′ over the code paths (the 9 files) | same |
| `checks/g44-03-controls.txt` | G44-03 recount of round 1's `Assumptions` control logs (`$SP/g44/run/asm/rule10/`) | shell recount (`grep -c`), round 1's raw logs |
| `checks/tools/` | `chk44r2.py`, `gitlib.py` (round 1's), `commentstrip.py`, `mksrc44r2.py` | written for this round |
| `landing/mergetrees-r2.txt` | the scratch merge commits and trees (`git merge-tree --write-tree`) | maintainer job log |
| `replay/tree/`, `replay/order/`, `replay/plan/`, `replay/state/` | the `cp -al` copy of `$SP/olean-replay-g44`, the T44′ export, downorder/fullorder (vs T44), the plan (10 build / 1417 reuse) on a copy of round 1's state (`copied.sha256`), the state update | round 1's tools, unmodified (`replay/tools/tools-*.sha256`) |
| `replay/build/` | `results.jsonl`, `per-module.tsv`, `permod.out`, the 10 module logs, `statecheck*` (1427 RESULT OK) | `run-build-g44b.sh` → `runner.py` → `scripts/lean_check_tree.sh` |
| `replay/checks/` | link counts and the olean comparison with round 1's T44 oleans; snapshot #4 rehash before, after and final (0/0/0); round 1's map rechecks; the deletion record of `$SP/olean-replay-g44` | `snapmap.py`, `mapnoml.py`, `stat`, `cmp` |
| `replay/output-map/` | the map of `$SP/olean-replay-g44b` without Mathlib (`fca1b6a3…`) and its comparison | `mapnoml.py` |
| `replay/admissions/` | `tipcensus.py` at T44 and T44′ (196 each, per-module identical) and the record sets | round 1's tool |
| `replay/axioms/` | `Axioms44.lean` (round 1's probe), its run record and log, `axsum.txt` | `runner_full.py` |
| `replay/lint/` | `campaign_style_lint.py --check8b` at T44′, non-INFO comparison with round 1's T44 run, INFO diff, `style_lint.py` and `sk15` on the three files | `scripts/` at T44′ |
| `rule10/statements/` | `touched.py`, records tip → T44′, over the 9 files | round 1's harness |
| `rule10/collector/` | the collector over #346's eight owners: probe source, run record, log (byte-identical to round 1's) | `rule10_g44b.sh collect` |
| `rule10/seal/` | coe-A seal records, probe sources, run records and logs for `Draws`, `Words`, `Handler`, `BonehBoyenMachine`; `seals-coe-A.tsv`; `error-forms-seal-runs.txt`; `sealcarry.txt` (comparison with round 1's records) | `rule10_g44b.sh coeA`, `sealcarry.py` |
| `records/` | `findings-r1.md`, `resolutions-r1.md`, `dispatch-r1.md`, `SHA256SUMS-r1`; the plan's Gate 44 rows, ledger rows DL-55/DL-56 and § Stage 2 at the pin; `corrections/` the two REPORTs and the review as filed in the staging commit, with `corrections.diff` against the pin | records branch |
| `pr/pr-rest-fields-r2.json` | #340 and #346 REST fields and bodies at staging (05:58 UTC) | `gh api` |

## ===== verification-r2.zip:checks/series-r2.txt (this pack) =====

records tip 4f4a7592a54cf82fa04f96b83645d7936672614c: Records: G44-01 ruled (accept; DL-55, DL-56 repaid in Stage 2)
  signature: gpgsig 1, ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc, ns=git, verified True
  descends from round 1's pin 8f888790: True; from the replay tip 1d1a9bb3: True
  code paths changed 1d1a9bb3..tip: 0; records commits 1d1a9bb3..tip: 19
    997aac33ab63 Records: Gate 44 round 1 staged (pairing fills #340 T1, #346 T4; Codex)
    a6a3c9b2b7d3 Records: Gate 44 round 1 finalized (pin 8f888790; seal supplement; PR descriptions)
    856e1c4496fd Records: Gate 44 round 1 staged
    465343ddf92a Records: Gate 44 round 1 dispatched
    86f645761519 Records: Lean parallelism ruling for cloud workers
    c0f52d90ad51 Records: local hosts allow up to 3 concurrent Lean processes
    8b219308d124 Records: #353 merged (Lean parallelism in workflow.md)
    54b18e4a6b96 Records: GSW phase 6a final delivered; review under way
    62df03f97f92 Records: bb1-sim fill checkpoint 1 review (proceed with notes)
    b9860ca888b1 Records: GSW 6a checkpoint 1 review (proceed with notes)
    084bb8a13d7c Records: cleanup Stage 1 checkpoint 1 review (proceed with notes)
    c3689193d98b Records: CS1-C1-Q1 ruled (keep S1-27; DL-53)
    fa29ab0a9193 Records: GSW phase 6a final phase-1 review (interim accept; LE-ren proposed)
    84d144b565bd Records: phase 6a rulings Q1-Q4 (LE-ren; DL-54)
    b2e89c107da0 Records: Gate 44 round 1 findings (HOLD: G44-01 major)
    4f4a7592a54c Records: G44-01 ruled (accept; DL-55, DL-56 repaid in Stage 2)

LE-g44 98cb0e521a94e94c304c78348fb5d3033435a3ed: parents 89a18a8225be1b76166af12a15179da291747783 (= #346 round-1 head 89a18a82: True)
  author Claude <noreply@anthropic.com> 2026-11-17T05:46:57+00:00; committer Claude <noreply@anthropic.com>; gpgsig 1 ssh-ed25519 SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc ns=git verified=True; same key as the records tip: True
  subject: bb1-machine landing edit LE-g44: attribute the bounded sampler to Candidates.statClose_sampleBelowL (G44-02)
  message ends with the two required trailer lines (Co-Authored-By, Claude-Session): True
    14	5	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean
    4	1	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean
    4	1	TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean
  signature control: LE-g44 with one byte added to its committer line verifies: False (expected False)
  remote #346 branch land/pairings-bb1-machine at staging: 89a18a8225be1b76166af12a15179da291747783 (LE-g44 not pushed; the maintainer pushes it)
#346 new head 98cb0e52: merge base with the tip 7291f6b237fec75add1549c0992c174442180488 (= round 1's 7291f6b2: True); commits 8; merges 0
  git diff 7291f6b2..98cb0e52 = git diff tip...head (three-dot, GitHub view) byte for byte: True; 167213 bytes, sha256 116a4d09fcd40f8f7df73860467b4d0631c4226cee1006ee65532024b8b32ede
  8 files changed, 2756 insertions(+), 17 deletions(-)
  le-g44.diff.txt = git diff 89a18a82..98cb0e52: 6116 bytes, sha256 e81b86c82dcb31d9c301b7d3baef3f7b26b0112d4dbe432fbe3b19dbcfbf5823; 3 files changed, 22 insertions(+), 7 deletions(-)

## ===== verification-r2.zip:checks/le-r2.txt (this pack) =====

LE-g44 is comment-only: every comment removed (line comments, nested block comments incl. /-- and /-!, string
literals honoured; commentstrip.py), each file at the parent 89a18a82 and at LE-g44 98cb0e52 is byte-identical.

TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean
  blob 370854585440 -> 2a3be13146a3; lines 451 -> 460; max width (characters) 99 -> 99; tabs 0; trailing spaces 0
  stripped sha256 6538e35fbde891bb75201113ba81d3961d880881cf623b13efed6590060f2d91 -> 6538e35fbde891bb75201113ba81d3961d880881cf623b13efed6590060f2d91; comment characters 8068 -> 8866; CODE-EQUAL True
  control (a space after the first `:=` of the code): caught
  control (one code line duplicated): caught
  control (`theorem` -> `lemma` at the first theorem): caught
  hunks: 3; +14 / -5 lines
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean
  blob 7b87d999b322 -> e26e3bd2cead; lines 632 -> 635; max width (characters) 99 -> 99; tabs 0; trailing spaces 0
  stripped sha256 e577cc1632f4abdef0518e3f4fe1582090683497f5f9872f13d34e0c6b0a3c83 -> e577cc1632f4abdef0518e3f4fe1582090683497f5f9872f13d34e0c6b0a3c83; comment characters 11371 -> 11657; CODE-EQUAL True
  control (a space after the first `:=` of the code): caught
  control (one code line duplicated): caught
  control (`theorem` -> `lemma` at the first theorem): caught
  hunks: 1; +4 / -1 lines
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean
  blob e562056e372a -> ef54f7e62e5c; lines 899 -> 902; max width (characters) 100 -> 100; tabs 0; trailing spaces 0
  stripped sha256 357556c548fc4891b96a8cd9effd03025d528eca8254769f4f9e6c5f66b75a63 -> 357556c548fc4891b96a8cd9effd03025d528eca8254769f4f9e6c5f66b75a63; comment characters 12869 -> 13155; CODE-EQUAL True
  control (a space after the first `:=` of the code): caught
  control (one code line duplicated): caught
  control (`theorem` -> `lemma` at the first theorem): caught
  hunks: 1; +4 / -1 lines
other paths changed by LE-g44: []
RESULT OK

## ===== verification-r2.zip:checks/mergetrees-r2.txt (this pack) =====

tip x #340: tree ff87d8158f6ccfcf70a7b0b966fd9487e594c618 rc 0; tip x #346 (LE-g44 head): tree dc43dfe2bf433fa6663e449f62026bd1c8a7ad23 rc 0
T44' = (tip x #340) x #346' = (tip x #346') x #340 = (tip x #340) x (tip x #346'): bee027f0903d531b3a43511cea16bfa123210291 (scratch commits; all three orders give this tree, landing/mergetrees-r2.txt)
T44' vs tip, code paths: 9; all paths: 9
  M TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean: T44' blob 930b0480503d = 98cb0e52 blob: True
  M TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean: T44' blob 2f90345d4400 = 98cb0e52 blob: True
  A TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean: T44' blob 2a3be13146a3 = 98cb0e52 blob: True
  A TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean: T44' blob ef54f7e62e5c = 98cb0e52 blob: True
  A TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles.lean: T44' blob 2a792dbddbac = 98cb0e52 blob: True
  A TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Reduction.lean: T44' blob f010d7c340f6 = 98cb0e52 blob: True
  A TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean: T44' blob e26e3bd2cead = 98cb0e52 blob: True
  M TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean: T44' blob b0fc112a2460 = 98cb0e52 blob: True
  M TCSlib/Cryptography/Pairing/Assumptions.lean: T44' blob f38ea5b4b4fb = 916afc25 blob: True
T44 (round 1) vs T44', code paths: 3 ['M\tTCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean', 'M\tTCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean', 'M\tTCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean']
T44 vs T44', non-code paths: records only (63 paths, all under briefs/ or the plan files: True)
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean: T44 -> T44' CODE-EQUAL after comment stripping True
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean: T44 -> T44' CODE-EQUAL after comment stripping True
  TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean: T44 -> T44' CODE-EQUAL after comment stripping True
T44p.diff.txt = git diff tip T44' over code paths: 184092 bytes, sha256 cf3340f7ff133fb46dd2ce4935d5b04ba77e4bfccf040f2ad8e4f3263bef6b42
git diff T44 T44' over code paths = le-g44.diff.txt byte for byte: True

## ===== verification-r2.zip:checks/headers-r2.txt (this pack) =====

TCSlib/Cryptography/Pairing/Assumptions.lean: T44 = T44' blob True
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean: T44 = T44' blob True
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean: T44 = T44' blob True
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/Defs.lean: T44 = T44' blob True
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyen.lean: T44 = T44' blob True
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Reduction.lean: T44 = T44' blob True
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles.lean: T44 = T44' blob True
TCSlib/Cryptography/Candidates/DiscreteLog.lean: T44 = T44' blob True
TCSlib.lean: T44 = T44' blob True
T1, T4, T2, T3 and bb1_sidSecure live in the first three files, so their headers, statement prose and bodies are byte-identical to round 1.

## ===== verification-r2.zip:checks/sources-r2.txt (this pack) =====

source tags [KEY..., locator] per LE-g44 file at 89a18a82 and at LE-g44; NEW / GONE = pairs added / removed
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean: tags 5 -> 5; keys used ['BB04', 'PS10']; ## References entries ['BB04', 'PS10']; used keys without an entry: []
  "Theorem 52.3" occurrences 2 -> 2; each now marked context: True
  names `Candidates.sampleBelowL` 7, `Candidates.statClose_sampleBelowL` 4, `Cryptography/Candidates/DiscreteLog.lean` 2
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean: tags 3 -> 3; keys used ['BB04', 'PS10']; ## References entries ['BB04', 'PS10']; used keys without an entry: []
  "Theorem 52.3" occurrences 1 -> 1; each now marked context: True
  names `Candidates.sampleBelowL` 2, `Candidates.statClose_sampleBelowL` 1, `Cryptography/Candidates/DiscreteLog.lean` 1
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean: tags 5 -> 5; keys used ['BB04', 'PS10']; ## References entries ['BB04', 'PS10']; used keys without an entry: []
  "Theorem 52.3" occurrences 1 -> 1; each now marked context: True
  names `Candidates.sampleBelowL` 1, `Candidates.statClose_sampleBelowL` 1, `Cryptography/Candidates/DiscreteLog.lean` 1

TCSlib/Cryptography/Candidates/DiscreteLog.lean at T44' (blob a423be2b59a4, = 89a18a82's and the tip's: True); namespaces ['namespace TCSlib.Cryptography.Candidates', 'namespace ExpGroupGen']
  sampleBelowL at line 578 (docstring from line 574); header:
    def sampleBelowL (m k B T : ℕ) (r : List Bool) : Option ℕ :=
  statClose_sampleBelowL at line 618 (docstring from line 602); header:
    theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
        StatClose (fun b : Fin (n * n) → Bool => (sampleBelowL m (Nat.size m) n n (List.ofFn b)).getD 0)
          (fun x : Fin m => (x : ℕ)) ((1 / 2 : ℝ) ^ n) := by

## ===== verification-r2.zip:checks/g44-03-controls.txt (this pack) =====

G44-03 recount from round 1's raw control logs ($SP/g44/run/asm/rule10/seal-runs/mods; KS = strict, K = coe, per rule10_b.sh lines 19-20)
==> mkctl-strict.log <==
chosen ['SealA_Cryptography_Pairing_Assumptions', 'SealB_Cryptography_Pairing_Assumptions']
4 control probes; 25 expected sealed failures

==> mkctl-coe.log <==
chosen ['SealA_Cryptography_Pairing_Assumptions', 'SealB_Cryptography_Pairing_Assumptions']
4 control probes; 25 expected sealed failures
G44A_KS_ControlS_A_Cryptography_Pairing_Assumptions.log	error: 12	error( 0	sha256 14ef2a78dababb20
G44A_KS_ControlS_B_Cryptography_Pairing_Assumptions.log	error: 13	error( 0	sha256 7d12009769947766
G44A_KS_ControlU_A_Cryptography_Pairing_Assumptions.log	error: 0	error( 0	sha256 e3b0c44298fc1c14
G44A_KS_ControlU_B_Cryptography_Pairing_Assumptions.log	error: 0	error( 0	sha256 e3b0c44298fc1c14
G44A_K_ControlS_A_Cryptography_Pairing_Assumptions.log	error: 12	error( 0	sha256 bd8c856110ae04e1
G44A_K_ControlS_B_Cryptography_Pairing_Assumptions.log	error: 13	error( 0	sha256 dcb9a954dab1c23d
G44A_K_ControlU_A_Cryptography_Pairing_Assumptions.log	error: 0	error( 0	sha256 e3b0c44298fc1c14
G44A_K_ControlU_B_Cryptography_Pairing_Assumptions.log	error: 0	error( 0	sha256 e3b0c44298fc1c14
variant prefix K_: sealed probes 2, unsealed probes 2, sealed negatives 25
variant prefix KS_: sealed probes 2, unsealed probes 2, sealed negatives 25
ALL_OK True
ALL_OK True

## ===== verification-r2.zip:replay/build/per-module.tsv (this pack) =====

module	rc	err_colon	err_paren	errors	error_substr	sorry	warnings
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws	0	0	0	0	0	0	0
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words	0	0	0	0	0	0	0
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler	0	0	0	0	0	0	0
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Reduction	0	0	0	0	0	0	0
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles	0	0	0	0	0	0	0
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine	0	0	0	0	0	0	0
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity	0	0	0	0	0	2	2
TCSlib/Cryptography/AdvancedEncryption/IdentityBased	0	0	0	0	0	0	0
TCSlib/Cryptography/AdvancedEncryption	0	0	0	0	0	0	0
TCSlib	0	0	0	0	0	0	0

## ===== verification-r2.zip:replay/build/statecheck.out (this pack) =====

bee027f0 order 1427; bad 0 [] | RESULT OK

## ===== verification-r2.zip:replay/checks/rebuilt-linkcount.txt (this pack) =====

TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws	links 1	ilean no	sha 2ee4ffff967d29ea	g44 ae474d14eb123f21	same-as-g44 no	same-inode no
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words	links 1	ilean no	sha b9204f09a885e6ef	g44 07689d04cfc9fb4d	same-as-g44 no	same-inode no
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler	links 1	ilean no	sha 50a83caf7b9c797a	g44 519eff8c71e215ea	same-as-g44 no	same-inode no
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Reduction	links 1	ilean no	sha 89e630a38004d3ec	g44 89e630a38004d3ec	same-as-g44 yes	same-inode no
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Oracles	links 1	ilean no	sha 3bf256957e53beac	g44 3bf256957e53beac	same-as-g44 yes	same-inode no
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine	links 1	ilean no	sha 61849c71f8fc3d9e	g44 61849c71f8fc3d9e	same-as-g44 yes	same-inode no
TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity	links 1	ilean no	sha 5a94e27c8bccb04f	g44 5a94e27c8bccb04f	same-as-g44 yes	same-inode no
TCSlib/Cryptography/AdvancedEncryption/IdentityBased	links 1	ilean no	sha 5db6847cb7c22ea1	g44 5db6847cb7c22ea1	same-as-g44 yes	same-inode no
TCSlib/Cryptography/AdvancedEncryption	links 1	ilean no	sha c53a5b440108883e	g44 c53a5b440108883e	same-as-g44 yes	same-inode no
TCSlib	links 1	ilean no	sha b615a2dca86d3614	g44 b615a2dca86d3614	same-as-g44 yes	same-inode no

## ===== verification-r2.zip:replay/checks/g44-deleted.txt (this pack) =====

olean-replay-g44 (round 1 output, T44 33681cb8): map without Mathlib ded2f64d177fc73a55c8f55e0ad1bc4699392c2a53c7cfb45f9152b55ed4abda, 1458 entries, rechecked equal at 2026-11-17 06:03:12 (run/checks/g44-map-final.out); map file kept at $SP/g44/run/output-map/olean-replay-g44.map-33681cb8.noMathlib.tsv
files 1459, symlinks 3346; df before: 4885 MB free
deleted 2026-11-17T06:03:30Z; df after: 4893 MB free
vs run/output-map/olean-replay-g44b.map-bee027f0.noMathlib.tsv: equal 1458; changed 0 []; added []; removed []
map /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/olean-snapshot.map-463f2244.tsv sha256 6607620d725049c90b34a51a2ab891f1520fd0f576aaf3f9d51301222cee41e7; on disk 1453; extra 0; changed 0; missing 0; symlinks 0; other files 0; empty dirs 0; RESULT OK

## ===== verification-r2.zip:replay/output-map/map.out (this pack) =====

run/output-map/olean-replay-g44b.map-bee027f0.noMathlib.tsv: entries 1458; sha256 fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9
vs /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g44/run/output-map/olean-replay-g44.map-33681cb8.noMathlib.tsv: equal 1455; changed 3 ['TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws', 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler', 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words']; added []; removed []

## ===== verification-r2.zip:replay/admissions/census-T44-vs-T44p.txt (this pack) =====

per-module counts identical

## ===== verification-r2.zip:replay/axioms/axsum.txt (this pack) =====

TCSlib.Cryptography.AdvancedEncryption.IdentityBased.exists_bb1_distinguisher :: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1_sidSecure :: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.oracleImpl_zero_onSpec :: propext, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.oracleImpl_one_onSpec :: propext, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.oracleImpl_two_onSpec :: propext, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.ofFn_bb1Scheme_encPP :: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.ofFn_bb1Scheme_encSK :: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1Scheme_msgSpace_iff :: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.ofFn_bb1SimCt :: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Machine.abs_expect_bb1Sim_sub_distinguisherL_le :: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Machine.simulate_handler :: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Machine.expect_handlerMachine :: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Machine.abs_expect_runAccept_sub_le :: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1_sim_real :: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.bb1_sim_random :: propext, sorryAx, Classical.choice, Quot.sound
TCSlib.Cryptography.Pairing.BilinearGen.bdhAssumption_of_dbdhAssumption :: propext, Classical.choice, Quot.sound

## ===== verification-r2.zip:rule10/seal/seals-coe-A.tsv (this pack) =====

SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenMachine	2311	0	0	1	1	
SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenMachine_Draws	1644	0	0	1	1	
SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenMachine_Handler	2275	0	0	1	1	
SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenMachine_Words	2242	0	0	1	1	

## ===== verification-r2.zip:rule10/seal/sealcarry.txt (this pack) =====

SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenMachine_Draws: requests 1644 -> 1644; probe fa1e03a16effe607 -> 5643f9e8c94bd97f; source 4645417997e38df0 -> 4532190ccbb5709d; round-1 record rel/seals-coe/A
  rows identical: True
  requested equal: True
  term readers identical: True
  excluded terms identical: True
  insertions identical (kind, size, sha256): True
  round-1 probe minus insertions = T44 source: True
  round-2 probe minus insertions = T44' source: True
  record probe_sha256 = probe file (both): True
  record source_sha256 = tree blob (both): True
  probes identical after comment stripping: True
SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenMachine_Words: requests 2242 -> 2242; probe a3aeb83f8466535e -> 912cdfd6148d5982; source a31d6ac2a5c09d25 -> b1e454a97822036f; round-1 record seals-coe/A
  rows identical: True
  requested equal: True
  term readers identical: True
  excluded terms identical: True
  insertions identical (kind, size, sha256): True
  round-1 probe minus insertions = T44 source: True
  round-2 probe minus insertions = T44' source: True
  record probe_sha256 = probe file (both): True
  record source_sha256 = tree blob (both): True
  probes identical after comment stripping: True
SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenMachine_Handler: requests 2275 -> 2275; probe dba62c6132c67480 -> abcf49e36874bef5; source 5d0c96a0c0659a9b -> 63192cea1640c70d; round-1 record seals-coe/A
  rows identical: True
  requested equal: True
  term readers identical: True
  excluded terms identical: True
  insertions identical (kind, size, sha256): True
  round-1 probe minus insertions = T44 source: True
  round-2 probe minus insertions = T44' source: True
  record probe_sha256 = probe file (both): True
  record source_sha256 = tree blob (both): True
  probes identical after comment stripping: True
SealA_Cryptography_AdvancedEncryption_IdentityBased_BonehBoyenMachine: requests 2311 -> 2311; probe 0b9b35460ed38451 -> 0b9b35460ed38451; source 2df4a1af50aea337 -> 2df4a1af50aea337; round-1 record seals-coe/A
  rows identical: True
  requested equal: True
  term readers identical: True
  excluded terms identical: True
  insertions identical (kind, size, sha256): True
  round-1 probe minus insertions = T44 source: True
  round-2 probe minus insertions = T44' source: True
  record probe_sha256 = probe file (both): True
  record source_sha256 = tree blob (both): True
  probes identical after comment stripping: True
RESULT OK

## ===== le-g44.diff.txt (this pack) =====

diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean
index 370854585..2a3be1314 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean
@@ -21,7 +21,11 @@ Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (step
 `AdvancedEncryption/IdentityBased/BonehBoyen.lean` draws its exponents `α_1` and `r` uniformly
 from `Z_p`. The reduction machine draws them from blocks of fresh coins instead, by the rejection
 sampler `Candidates.sampleBelowL p (Nat.size p) n n` with `n = κ + wG(κ) + 1` and the fallback
-`0` (`draw`), which is within `(1/2)^n` of uniform (`statClose_draw`). This file gives
+`0` (`draw`), which is within `(1/2)^n` of uniform (`statClose_draw`). The bounded sampler and
+its bound are the library's existing construction, `Candidates.sampleBelowL` and
+`Candidates.statClose_sampleBelowL` (`Cryptography/Candidates/DiscreteLog.lean`): for
+`0 < m < 2^n` its output on `n · n` uniform coins, with the fallback `0`, is within `(1/2)^n` of
+the uniform number below `m`. This file gives
 * the simulator's oracles with the exponent supplied as an argument (`drawStep`), on the
   query and answer lengths of the machine (`qLen`, `aLen`), with their case lemmas;
 * the comparison of drawn and ideal exponents on a deterministic run: for a test with values
@@ -55,7 +59,10 @@ sampler `Candidates.sampleBelowL p (Nat.size p) n n` with `n = κ + wG(κ) + 1`
   (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the simulator
   in the proof of Theorem 4.1.
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-  (Theorem 52.3, sampling `Z_q` by rejection; Definition 181.1, statistical closeness.)
+  (Definition 181.1, statistical closeness. Context only: §2.8, Theorem 52.3, the discrete-log
+  collection, whose proof remarks that its domain `Z_q` is easy to sample; it does not give
+  this sampler, its coin budget, its fallback or its bound, which are the library's
+  `Candidates.sampleBelowL` and `Candidates.statClose_sampleBelowL`.)
 -/
 
 namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased
@@ -127,9 +134,11 @@ def blockLen : PolyExpr := (PolyExpr.var.add G.wG).add (.const 1)
 theorem blockLen_eval (κ : ℕ) : (blockLen G).eval κ = κ + G.wG.eval κ + 1 := by
   rw [blockLen, PolyExpr.eval_add, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
 
-/-- **An exponent of `Z_p` drawn from `n · n` coins** [PS10, Theorem 52.3]: the rejection sampler
-`sampleBelowL p (Nat.size p) n n` with the fallback `0`, read in `Z_p`, for the order `p` of the
-group described by `d` and `n = blockLen G κ`. -/
+/-- **An exponent of `Z_p` drawn from `n · n` coins**: the library's bounded rejection sampler
+`Candidates.sampleBelowL p (Nat.size p) n n` (`Cryptography/Candidates/DiscreteLog.lean`, whose
+bound `Candidates.statClose_sampleBelowL` gives `statClose_draw`) with the fallback `0`, read in
+`Z_p`, for the order `p` of the group described by `d` and `n = blockLen G κ`. That `Z_p` is
+easy to sample is the remark in the proof of [PS10, Theorem 52.3] (§2.8), context only. -/
 noncomputable def draw (κ : ℕ) (d : List Bool)
     (w : Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool) : ZMod (G.group κ d).order :=
   ((Candidates.sampleBelowL (G.group κ d).order (Nat.size (G.group κ d).order)
diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean
index e562056e3..ef54f7e62 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean
@@ -59,7 +59,10 @@ run is the run of `drawStep` with exponents read from a tape, through the encodi
   (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
   `B` in the proof of Theorem 4.1.
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-  (Algorithm 43.2, the extended Euclidean algorithm; Theorem 52.3, sampling `Z_q`.)
+  (Algorithm 43.2, the extended Euclidean algorithm. Context only: §2.8, Theorem 52.3, the
+  discrete-log collection, whose proof remarks that its domain `Z_q` is easy to sample; it does
+  not give the bounded sampler or its bound, which are the library's `Candidates.sampleBelowL`
+  and `Candidates.statClose_sampleBelowL`, `Cryptography/Candidates/DiscreteLog.lean`.)
 -/
 
 namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased
diff --git a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean
index 7b87d999b..e26e3bd2c 100644
--- a/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean
+++ b/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean
@@ -57,7 +57,10 @@ seed by `Candidates.sampleBelowL` and writes it with `wG(κ) + 1` bits.
   (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
   `B` in the proof of Theorem 4.1.
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-  (Algorithm 43.2, the extended Euclidean algorithm; Theorem 52.3, sampling `Z_q`.)
+  (Algorithm 43.2, the extended Euclidean algorithm. Context only: §2.8, Theorem 52.3, the
+  discrete-log collection, whose proof remarks that its domain `Z_q` is easy to sample; it does
+  not give the bounded sampler or its bound, which are the library's `Candidates.sampleBelowL`
+  and `Candidates.statClose_sampleBelowL`, `Cryptography/Candidates/DiscreteLog.lean`.)
 -/
 
 namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Draws.lean (Lean, at 98cb0e521a94e94c304c78348fb5d3033435a3ed) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator with its exponents drawn from coin blocks

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (step 3 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). The simulator `bb1SimImpl` of
`AdvancedEncryption/IdentityBased/BonehBoyen.lean` draws its exponents `α_1` and `r` uniformly
from `Z_p`. The reduction machine draws them from blocks of fresh coins instead, by the rejection
sampler `Candidates.sampleBelowL p (Nat.size p) n n` with `n = κ + wG(κ) + 1` and the fallback
`0` (`draw`), which is within `(1/2)^n` of uniform (`statClose_draw`). The bounded sampler and
its bound are the library's existing construction, `Candidates.sampleBelowL` and
`Candidates.statClose_sampleBelowL` (`Cryptography/Candidates/DiscreteLog.lean`): for
`0 < m < 2^n` its output on `n · n` uniform coins, with the fallback `0`, is within `(1/2)^n` of
the uniform number below `m`. This file gives
* the simulator's oracles with the exponent supplied as an argument (`drawStep`), on the
  query and answer lengths of the machine (`qLen`, `aLen`), with their case lemmas;
* the comparison of drawn and ideal exponents on a deterministic run: for a test with values
  `0` and `1` of `cap` exponents, `cap` drawn exponents change its average by at most
  `cap · (1/2)^n` (`abs_expect_draws_sub_le`, from `statClose_draw` and
  `OneWay.statClose_pi`);
* determinism of the run of `drawStep` with exponents read from a tape
  (`exists_simulate_tape_eq_pure`).

## Main definitions

* `BB1Machine.qLen`, `BB1Machine.aLen` — the query and answer lengths of the three oracles.
* `BB1Machine.blockLen` — the sampler's width `n = κ + wG(κ) + 1`.
* `BB1Machine.draw` — an exponent of `Z_p` drawn from `n · n` coins.
* `BB1Machine.drawStep` — the simulator's oracles with the exponent given.

## Main results

* `BB1Machine.qLen_eval`, `BB1Machine.aLen_eval` — the lengths are the game's.
* `BB1Machine.statClose_draw` — a drawn exponent is `(1/2)^n`-close to uniform.
* `BB1Machine.drawStep_zero`, `BB1Machine.drawStep_one_none`, …,
  `BB1Machine.drawStep_two_invalid` — the case lemmas.
* `BB1Machine.exists_drawStep_eq_pure`, `BB1Machine.exists_simulate_tape_eq_pure` — the oracles
  and their runs from a tape are deterministic.
* `BB1Machine.abs_expect_draws_sub_le` — drawn against ideal exponents.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the simulator
  in the proof of Theorem 4.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 181.1, statistical closeness. Context only: §2.8, Theorem 52.3, the discrete-log
  collection, whose proof remarks that its domain `Z_q` is easy to sample; it does not give
  this sampler, its coin budget, its fallback or its bound, which are the library's
  `Candidates.sampleBelowL` and `Candidates.statClose_sampleBelowL`.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Machine

variable (G : BilinearGen) (ℓ : PolyExpr)

/-! ### Lengths -/

/-- The query lengths of the three oracles as polynomials: identities for `Init` (`0`) and
`KeyGen` (`1`), two messages for `Challenge` (`2`). -/
noncomputable def qLen : Fin 3 → PolyExpr
  | 0 => (bb1Scheme G ℓ).idLen
  | 1 => (bb1Scheme G ℓ).idLen
  | 2 => (bb1Scheme G ℓ).msgLen.add (bb1Scheme G ℓ).msgLen

/-- `qLen G ℓ 0 = idLen`. -/
theorem qLen_zero : qLen G ℓ 0 = (bb1Scheme G ℓ).idLen := rfl

/-- `qLen G ℓ 1 = idLen`. -/
theorem qLen_one : qLen G ℓ 1 = (bb1Scheme G ℓ).idLen := rfl

/-- `qLen G ℓ 2 = msgLen + msgLen`. -/
theorem qLen_two : qLen G ℓ 2 = (bb1Scheme G ℓ).msgLen.add (bb1Scheme G ℓ).msgLen := rfl

/-- The answer lengths of the three oracles as polynomials: parameters for `Init`, a validity
bit and a key for `KeyGen`, a ciphertext for `Challenge`. -/
noncomputable def aLen : Fin 3 → PolyExpr
  | 0 => (bb1Scheme G ℓ).ppLen
  | 1 => (bb1Scheme G ℓ).skLen.add (.const 1)
  | 2 => (bb1Scheme G ℓ).ctLen

/-- `aLen G ℓ 0 = ppLen`. -/
theorem aLen_zero : aLen G ℓ 0 = (bb1Scheme G ℓ).ppLen := rfl

/-- `aLen G ℓ 1 = skLen + 1`. -/
theorem aLen_one : aLen G ℓ 1 = (bb1Scheme G ℓ).skLen.add (.const 1) := rfl

/-- `aLen G ℓ 2 = ctLen`. -/
theorem aLen_two : aLen G ℓ 2 = (bb1Scheme G ℓ).ctLen := rfl

/-- The query lengths are the game's: `(qLen G ℓ ·).eval κ = (bb1Scheme G ℓ).inLens κ`. -/
theorem qLen_eval (κ : ℕ) : (fun i => (qLen G ℓ i).eval κ) = (bb1Scheme G ℓ).inLens κ := by
  funext i
  match i with
  | 0 => rw [qLen_zero, IBEScheme.inLens_zero]
  | 1 => rw [qLen_one, IBEScheme.inLens_one]
  | 2 => rw [qLen_two, PolyExpr.eval_add, IBEScheme.inLens_two]

/-- The answer lengths are the game's: `(aLen G ℓ ·).eval κ = (bb1Scheme G ℓ).outLens κ`. -/
theorem aLen_eval (κ : ℕ) : (fun i => (aLen G ℓ i).eval κ) = (bb1Scheme G ℓ).outLens κ := by
  funext i
  match i with
  | 0 => rw [aLen_zero, IBEScheme.outLens_zero]
  | 1 => rw [aLen_one, PolyExpr.eval_add, PolyExpr.eval_const, IBEScheme.outLens_one]
  | 2 => rw [aLen_two, IBEScheme.outLens_two]

/-! ### Exponents drawn from coins -/

/-- The width `n = κ + wG(κ) + 1` of the exponent sampler (Gate 40, G40-03): `n` trials of
`n`-bit blocks. -/
def blockLen : PolyExpr := (PolyExpr.var.add G.wG).add (.const 1)

/-- `(blockLen G).eval κ = κ + wG(κ) + 1`. -/
theorem blockLen_eval (κ : ℕ) : (blockLen G).eval κ = κ + G.wG.eval κ + 1 := by
  rw [blockLen, PolyExpr.eval_add, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]

/-- **An exponent of `Z_p` drawn from `n · n` coins**: the library's bounded rejection sampler
`Candidates.sampleBelowL p (Nat.size p) n n` (`Cryptography/Candidates/DiscreteLog.lean`, whose
bound `Candidates.statClose_sampleBelowL` gives `statClose_draw`) with the fallback `0`, read in
`Z_p`, for the order `p` of the group described by `d` and `n = blockLen G κ`. That `Z_p` is
easy to sample is the remark in the proof of [PS10, Theorem 52.3] (§2.8), context only. -/
noncomputable def draw (κ : ℕ) (d : List Bool)
    (w : Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool) : ZMod (G.group κ d).order :=
  ((Candidates.sampleBelowL (G.group κ d).order (Nat.size (G.group κ d).order)
    ((blockLen G).eval κ) ((blockLen G).eval κ) (List.ofFn w)).getD 0 : ℕ)

/-- `draw G κ d w = ((sampleBelowL p (Nat.size p) n n ⟦w⟧).getD 0 : Z_p)`. -/
theorem draw_eq (κ : ℕ) (d : List Bool)
    (w : Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool) :
    draw G κ d w = ((Candidates.sampleBelowL (G.group κ d).order
      (Nat.size (G.group κ d).order) ((blockLen G).eval κ) ((blockLen G).eval κ)
      (List.ofFn w)).getD 0 : ℕ) := rfl

/-- The order of a bilinear group with `wG`-bit encodings is at most `2^{wG}`:
`(G.group κ d).order ≤ 2 ^ wG(κ)` (the encoding of `G` is injective). -/
theorem order_le_two_pow (κ : ℕ) (d : List Bool) : (G.group κ d).order ≤ 2 ^ G.wG.eval κ := by
  rw [← (G.group κ d).card_G]
  calc Fintype.card (G.group κ d).G ≤ Fintype.card (Fin (G.wG.eval κ) → Bool) :=
        Fintype.card_le_of_injective _ (G.group κ d).encG_injective
    _ = 2 ^ G.wG.eval κ := by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **A drawn exponent is `(1/2)^n`-close to uniform** on `Z_p` (Gate 40, G40-03): `0 < p` and
`p ≤ 2^{wG(κ)} < 2^n`, so `statClose_sampleBelowL` applies.

**Proof sketch.** `statClose_sampleBelowL` with `m = p`, mapped into `Z_p` by the cast
(`StatClose.map`); the uniform element of `Fin p` cast into `Z_p` is the uniform element of `Z_p`
along the bijection `x ↦ x.val` (`StatClose.comp_equiv_right`, `ZMod.natCast_zmod_val`). -/
theorem statClose_draw (κ : ℕ) (d : List Bool) :
    StatClose (draw G κ d) (id : ZMod (G.group κ d).order → ZMod (G.group κ d).order)
      ((1 / 2 : ℝ) ^ (blockLen G).eval κ) := by
  set p := (G.group κ d).order with hp
  have hm : 0 < p := (G.group κ d).order_prime.pos
  have hmn : p < 2 ^ (blockLen G).eval κ := by
    rw [blockLen_eval]
    calc p ≤ 2 ^ G.wG.eval κ := order_le_two_pow G κ d
      _ < 2 ^ (κ + G.wG.eval κ + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  let e : ZMod p ≃ Fin p :=
    { toFun := fun t => ⟨t.val, ZMod.val_lt t⟩
      invFun := fun x => ((x : ℕ) : ZMod p)
      left_inv := fun t => ZMod.natCast_zmod_val t
      right_inv := fun x => Fin.ext (by
        show ((x : ℕ) : ZMod p).val = x
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt x.2]) }
  have h := ((Candidates.statClose_sampleBelowL hm hmn).map
    fun v : ℕ => (v : ZMod p)).comp_equiv_right e
  have hX : (fun b : Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool =>
      (((Candidates.sampleBelowL p (Nat.size p) ((blockLen G).eval κ) ((blockLen G).eval κ)
        (List.ofFn b)).getD 0 : ℕ) : ZMod p)) = draw G κ d :=
    funext fun b => (draw_eq G κ d b).symm
  have hY : (fun t : ZMod p => (((e t : Fin p) : ℕ) : ZMod p)) = id :=
    funext fun t => ZMod.natCast_zmod_val t
  rw [hX, hY] at h
  exact h

/-! ### The simulator's oracles with the exponent given -/

open Classical in
/-- **The simulator's oracles with the exponent `u` supplied**, on the lengths `qLen`, `aLen`,
answering with the words of BB1's encodings: the oracles of `bb1SimImpl` [BB04, proof of
Theorem 4.1] with the uniform exponent replaced by `u`.
* `Init` on `ID`: with `(ID*, α_1)` the recorded pair, or `(ID, u)` before a commitment (which it
  records), the word `d ‖ g ‖ X ‖ Y ‖ h` of the parameters `(g, X, Y, h)`,
  `h = X^{(−ID*).val} · g^{α_1.val}`.
* `KeyGen` on `ID`: `⊥` before `Init` or for `ID = ID*`; otherwise `1 ‖ d_0 ‖ d_1` with
  `d_0 = Y^{(−α_1/(ID − ID*)).val} · F(ID)^{u.val}`, `F(ID) = X^{ID.val} · h`, and
  `d_1 = Y^{(−1/(ID − ID*)).val} · g^{u.val}`.
* `Challenge` on `M_0 ‖ M_1`: `⊥` before `Init`; the recorded challenge once there is one;
  otherwise, if both halves are encodings of `G_T`, the word `M_b · T ‖ Z ‖ Z^{α_1.val}`, recorded;
  `⊥` if not.
Identities are read in `Z_p` by `BB1.idToZ` and messages decoded by `BB1.decodeT`. -/
noncomputable def drawStep (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT) :
    ∀ i : Fin 3, (Fin ((qLen G ℓ i).eval κ) → Bool) → BB1SimState G ℓ κ d →
      ZMod (G.group κ d).order →
        ProbComp ((Fin ((aLen G ℓ i).eval κ) → Bool) × BB1SimState G ℓ κ d)
  | 0, x, s, u =>
    .pure (padFin _ (d ++ List.ofFn ((G.group κ d).encG g) ++ List.ofFn ((G.group κ d).encG X) ++
        List.ofFn ((G.group κ d).encG Y) ++ List.ofFn ((G.group κ d).encG
          (X ^ (-BB1.idToZ (G.group κ d) (s.1.getD (padFin _ (List.ofFn x), u)).1).val *
            g ^ (s.1.getD (padFin _ (List.ofFn x), u)).2.val))),
      (some (s.1.getD (padFin _ (List.ofFn x), u)), s.2))
  | 1, x, s, u =>
    match s.1 with
    | some (t, α₁) =>
      if List.ofFn x = List.ofFn t then .pure (zeroBits _, s)
      else .pure (padFin _ (true :: (List.ofFn ((G.group κ d).encG
          (Y ^ (-α₁ / (BB1.idToZ (G.group κ d)
              (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) -
              BB1.idToZ (G.group κ d) t)).val *
            (X ^ (BB1.idToZ (G.group κ d)
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x))).val *
              (X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val)) ^ u.val)) ++
          List.ofFn ((G.group κ d).encG
            (Y ^ (-1 / (BB1.idToZ (G.group κ d)
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) -
              BB1.idToZ (G.group κ d) t)).val * g ^ u.val)))), s)
    | none => .pure (zeroBits _, s)
  | 2, mm, s, _ =>
    match s.1, s.2 with
    | some _, some c => .pure (padFin _ (List.ofFn c), s)
    | some (_, α₁), none =>
      if (∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
          (∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ)) then
        .pure (padFin _ (List.ofFn ((G.group κ d).encT (BB1.decodeT (G.group κ d)
            (padFin _ (if b then (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ)
              else (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ))) * T)) ++
            List.ofFn ((G.group κ d).encG Z) ++ List.ofFn ((G.group κ d).encG (Z ^ α₁.val))),
          (s.1, some (padFin _ (List.ofFn ((G.group κ d).encT (BB1.decodeT (G.group κ d)
            (padFin _ (if b then (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ)
              else (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ))) * T)) ++
            List.ofFn ((G.group κ d).encG Z) ++ List.ofFn ((G.group κ d).encG (Z ^ α₁.val))))))
      else .pure (zeroBits _, s)
    | none, _ => .pure (zeroBits _, s)

section Cases

variable (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G) (T : (G.group κ d).GT)

/-- **`Init`**: with `(t, α) = s.1.getD (ID, u)` (the recorded pair, or the query and `u` before a
commitment), the answer is the padded word `d ‖ g ‖ X ‖ Y ‖ X^{(−t).val} g^{α.val}` and the state
records `(t, α)`. -/
theorem drawStep_zero (x : Fin ((qLen G ℓ 0).eval κ) → Bool) (s : BB1SimState G ℓ κ d)
    (u : ZMod (G.group κ d).order) :
    drawStep G ℓ b κ d g X Y Z T 0 x s u =
      .pure (padFin _ (d ++ List.ofFn ((G.group κ d).encG g) ++
          List.ofFn ((G.group κ d).encG X) ++ List.ofFn ((G.group κ d).encG Y) ++
          List.ofFn ((G.group κ d).encG
            (X ^ (-BB1.idToZ (G.group κ d) (s.1.getD (padFin _ (List.ofFn x), u)).1).val *
              g ^ (s.1.getD (padFin _ (List.ofFn x), u)).2.val))),
        (some (s.1.getD (padFin _ (List.ofFn x), u)), s.2)) :=
  rfl

/-- **`KeyGen` before `Init`** answers `⊥` and keeps the state. -/
theorem drawStep_one_none (x : Fin ((qLen G ℓ 1).eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (u : ZMod (G.group κ d).order) :
    drawStep G ℓ b κ d g X Y Z T 1 x (none, c) u = .pure (zeroBits _, (none, c)) :=
  rfl

/-- **`KeyGen` for the committed identity** (equal words) answers `⊥` and keeps the state. -/
theorem drawStep_one_target (x : Fin ((qLen G ℓ 1).eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (u : ZMod (G.group κ d).order)
    (h : List.ofFn x = List.ofFn t) :
    drawStep G ℓ b κ d g X Y Z T 1 x (some (t, α₁), c) u =
      .pure (zeroBits _, (some (t, α₁), c)) := by
  show (if List.ofFn x = List.ofFn t then _ else _) = _
  rw [if_pos h]

/-- **`KeyGen` for another identity** answers the padded word `1 ‖ d_0 ‖ d_1` of the simulated
key with `r = u` and keeps the state.

**Proof sketch.** The committed branch of `drawStep` at index `1` is the test `⟦x⟧ = ⟦t⟧`;
it fails by `h`. -/
theorem drawStep_one_key (x : Fin ((qLen G ℓ 1).eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (u : ZMod (G.group κ d).order)
    (h : List.ofFn x ≠ List.ofFn t) :
    drawStep G ℓ b κ d g X Y Z T 1 x (some (t, α₁), c) u =
      .pure (padFin _ (true :: (List.ofFn ((G.group κ d).encG
          (Y ^ (-α₁ / (BB1.idToZ (G.group κ d)
              (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) -
              BB1.idToZ (G.group κ d) t)).val *
            (X ^ (BB1.idToZ (G.group κ d)
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x))).val *
              (X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val)) ^ u.val)) ++
          List.ofFn ((G.group κ d).encG
            (Y ^ (-1 / (BB1.idToZ (G.group κ d)
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) -
              BB1.idToZ (G.group κ d) t)).val * g ^ u.val)))), (some (t, α₁), c)) := by
  show (if List.ofFn x = List.ofFn t then _ else _) = _
  rw [if_neg h]

/-- **`Challenge` before `Init`** answers `⊥` and keeps the state. -/
theorem drawStep_two_none (mm : Fin ((qLen G ℓ 2).eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (u : ZMod (G.group κ d).order) :
    drawStep G ℓ b κ d g X Y Z T 2 mm (none, c) u = .pure (zeroBits _, (none, c)) :=
  rfl

/-- **`Challenge` after a recorded challenge** repeats it. -/
theorem drawStep_two_repeat (mm : Fin ((qLen G ℓ 2).eval κ) → Bool)
    (tα : (Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order)
    (w : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) (u : ZMod (G.group κ d).order) :
    drawStep G ℓ b κ d g X Y Z T 2 mm (some tα, some w) u =
      .pure (padFin _ (List.ofFn w), (some tα, some w)) :=
  rfl

open Classical in
/-- **The first `Challenge` with both halves in `G_T`** answers and records the padded word
`M_b · T ‖ Z ‖ Z^{α_1.val}`, `M_b` the decoded half selected by `b`.

**Proof sketch.** The branch of `drawStep` at index `2` with a commitment and no recorded
challenge is the test that both halves encode elements of `G_T`; it holds by `h`. -/
theorem drawStep_two_fresh (mm : Fin ((qLen G ℓ 2).eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (u : ZMod (G.group κ d).order)
    (h : (∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
          (∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ))) :
    drawStep G ℓ b κ d g X Y Z T 2 mm (some (t, α₁), none) u =
      .pure (padFin _ (List.ofFn ((G.group κ d).encT (BB1.decodeT (G.group κ d)
            (padFin _ (if b then (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ)
              else (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ))) * T)) ++
            List.ofFn ((G.group κ d).encG Z) ++ List.ofFn ((G.group κ d).encG (Z ^ α₁.val))),
          (some (t, α₁), some (padFin _ (List.ofFn ((G.group κ d).encT (BB1.decodeT
            (G.group κ d) (padFin _ (if b then (List.ofFn mm).drop
              ((bb1Scheme G ℓ).msgLen.eval κ) else (List.ofFn mm).take
                ((bb1Scheme G ℓ).msgLen.eval κ))) * T)) ++
            List.ofFn ((G.group κ d).encG Z) ++
              List.ofFn ((G.group κ d).encG (Z ^ α₁.val)))))) := by
  show (if _ then _ else _) = _
  rw [if_pos h]

open Classical in
/-- **The first `Challenge` with a half outside `G_T`** answers `⊥` and keeps the state. -/
theorem drawStep_two_invalid (mm : Fin ((qLen G ℓ 2).eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (u : ZMod (G.group κ d).order)
    (h : ¬ ((∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
          (∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ)))) :
    drawStep G ℓ b κ d g X Y Z T 2 mm (some (t, α₁), none) u =
      .pure (zeroBits _, (some (t, α₁), none)) := by
  show (if _ then _ else _) = _
  rw [if_neg h]

/-- **The oracles with the exponent given are deterministic**: every call returns one answer and
one new state.

**Proof sketch.** Cases on the oracle, the commitment, the recorded challenge and the tests, each
closed by its case lemma (`drawStep_zero`, `drawStep_one_none`, `drawStep_one_target`,
`drawStep_one_key`, `drawStep_two_none`, `drawStep_two_fresh`, `drawStep_two_invalid`,
`drawStep_two_repeat`). -/
theorem exists_drawStep_eq_pure (i : Fin 3) (x : Fin ((qLen G ℓ i).eval κ) → Bool)
    (s : BB1SimState G ℓ κ d) (u : ZMod (G.group κ d).order) :
    ∃ y s', drawStep G ℓ b κ d g X Y Z T i x s u = .pure (y, s') := by
  classical
  obtain ⟨o, c⟩ := s
  match i, x with
  | 0, x => exact ⟨_, _, drawStep_zero G ℓ b κ d g X Y Z T x (o, c) u⟩
  | 1, x =>
    rcases o with _ | ⟨t, α₁⟩
    · exact ⟨_, _, drawStep_one_none G ℓ b κ d g X Y Z T x c u⟩
    · by_cases h : List.ofFn x = List.ofFn t
      · exact ⟨_, _, drawStep_one_target G ℓ b κ d g X Y Z T x t α₁ c u h⟩
      · exact ⟨_, _, drawStep_one_key G ℓ b κ d g X Y Z T x t α₁ c u h⟩
  | 2, x =>
    rcases o with _ | ⟨t, α₁⟩
    · exact ⟨_, _, drawStep_two_none G ℓ b κ d g X Y Z T x c u⟩
    · rcases c with _ | w
      · by_cases h : (∃ v, List.ofFn ((G.group κ d).encT v) =
              (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
            (∃ v, List.ofFn ((G.group κ d).encT v) =
              (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ))
        · exact ⟨_, _, drawStep_two_fresh G ℓ b κ d g X Y Z T x t α₁ u h⟩
        · exact ⟨_, _, drawStep_two_invalid G ℓ b κ d g X Y Z T x t α₁ u h⟩
      · exact ⟨_, _, drawStep_two_repeat G ℓ b κ d g X Y Z T x (t, α₁) w u⟩

/-- **Runs from a tape are deterministic**: with the exponent of the `j`-th query read from a
tape `V j` (`ETTGame.tapeImpl`), the run of any computation returns one output and one final
state.

**Proof sketch.** Induction on the computation; each call is deterministic
(`exists_drawStep_eq_pure`, `ETTGame.tapeImpl_apply`). -/
theorem exists_simulate_tape_eq_pure (V : ℕ → ZMod (G.group κ d).order) {α : Type}
    (c : OracleComp (bitSpec (fun i => (qLen G ℓ i).eval κ) (fun i => (aLen G ℓ i).eval κ)) α)
    (st : BB1SimState G ℓ κ d × ℕ) :
    ∃ a st', simulate (ETTGame.tapeImpl (drawStep G ℓ b κ d g X Y Z T) V) c st =
      .pure (a, st') := by
  induction c generalizing st with
  | pure a => exact ⟨a, st, simulate_pure _ a st⟩
  | query i x k ih =>
    obtain ⟨y, s', h⟩ := exists_drawStep_eq_pure G ℓ b κ d g X Y Z T i x st.1 (V st.2)
    obtain ⟨a, st', hk⟩ := ih y (s', st.2 + 1)
    refine ⟨a, st', ?_⟩
    rw [simulate_query, ETTGame.tapeImpl_apply, h, OracleComp.pure_bind, OracleComp.pure_bind]
    exact hk

end Cases

/-! ### Drawn against ideal exponents -/

/-- A function with values `0` and `1` averages to the probability of the value `1`:
`𝔼_{x ← α} Φ x = Pr_{x ← α}[Φ x = 1]` (`prob_sample_eq_uprob`). -/
private theorem expect_sample_eq_uprob {α : Type} [Fintype α] [Nonempty α] (Φ : α → ℝ)
    (hΦ : ∀ x, Φ x = 0 ∨ Φ x = 1) :
    ProbComp.expect (ProbComp.sample α) Φ = uprob fun x => Φ x = 1 := by
  classical
  have h : Φ = fun x => if Φ x = 1 then 1 else 0 := by
    funext x
    rcases hΦ x with h0 | h1
    · rw [h0, if_neg zero_ne_one]
    · rw [h1, if_pos rfl]
  rw [← Bridge.prob_sample_eq_uprob, ProbComp.prob_eq_expect]
  conv_lhs => rw [h]

/-- **Drawn exponents against ideal ones, on a test with values `0` and `1`**: for `cap`
exponents and any `Φ` with values in `{0, 1}`,
`|𝔼_{T} Φ(draw ∘ T) − 𝔼_{U ← Z_p^cap} Φ(U)| ≤ cap · (1/2)^n`, `T` uniform over `cap` blocks of
`n · n` coins.

**Proof sketch.** Both averages are probabilities of the event `Φ = 1`
(`prob_sample_eq_uprob`); `cap` independent draws are `cap · (1/2)^n`-close to `cap` uniform
exponents (`statClose_draw`, `OneWay.statClose_pi`), and the event is a test set. -/
theorem abs_expect_draws_sub_le (κ : ℕ) (d : List Bool) (cap : ℕ)
    (Φ : (Fin cap → ZMod (G.group κ d).order) → ℝ) (hΦ : ∀ U, Φ U = 0 ∨ Φ U = 1) :
    |ProbComp.expect
        (ProbComp.sample (Fin cap → Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool))
        (fun T => Φ fun j => draw G κ d (T j)) -
      ProbComp.expect (ProbComp.sample (Fin cap → ZMod (G.group κ d).order)) Φ| ≤
      cap * (1 / 2 : ℝ) ^ (blockLen G).eval κ := by
  rw [expect_sample_eq_uprob _ fun T => hΦ _, expect_sample_eq_uprob Φ hΦ]
  exact (OneWay.statClose_pi (statClose_draw G κ d) cap).abs_uprob_sub_le fun U => Φ U = 1

end BB1Machine

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Words.lean (Lean, at 98cb0e521a94e94c304c78348fb5d3033435a3ed) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Draws
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The string layer of the BB1 reduction handler

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (step 3 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): the string functions from which the handler of
`BonehBoyenMachine/Handler.lean` is assembled, each polynomial-time, with its value on the inputs
the handler sees.

**The round input.** One round of the handler (`Games.PolyHandler`) reads
`w = ⟨⟨1^κ, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` (`PolyHandler.input`): the parameter, the reduction input
`z = ⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩` (`Pairing.tupleStr`), the seed `ω`, the state
`s = ⟨1^j, ⟨o_1, o_2⟩⟩` (padded), the oracle index and the query. The readers are named after the
field they read: `rU`, `rZ`, `rW`, `rS`, `rI`, `rX` (the round input), `zD`, …, `zT` (the tuple),
`sJ`, `sO1`, `sR`, `sCom`, `sChal`, `sC`, `sO2`, `kT`, `kA` (the state).

**Arithmetic and groups.** Residues modulo the order `p = ⟦orderStr d⟧` are binary numerals:
`modS`, `negS`, `addS`, `mulS`, `invS` compute `a mod p`, `−a`, `a + c`, `a · c`, `a⁻¹` (`0⁻¹ = 0`)
with the functions of `Candidates.ArithmeticFP` (negation through truncated subtraction of the
reduced residue from `p`, then a reduction); `mulGS`, `powGS` are the operations of `G` of the
contract `Pairing.BilinearGen.Ops`. `uS` draws the exponent of the query from block `j` of the
seed by `Candidates.sampleBelowL` and writes it with `wG(κ) + 1` bits.

## Main definitions

* `BB1Machine.aWidth`, `BB1Machine.nn` — the widths `wG + 1` and `n · n`.
* `BB1Machine.rU`, …, `BB1Machine.kA` — the readers of the round input.
* `BB1Machine.pS`, `modS`, `negS`, `addS`, `mulS`, `invS`, `mulGS`, `powGS` — arithmetic.
* `BB1Machine.blkS`, `BB1Machine.uS` — the block of the query and its exponent.

## Main results

* `BB1Machine.poly_rU`, …, `BB1Machine.poly_uS` — polynomial time.
* `BB1Machine.rU_input`, …, `BB1Machine.zT_of` — the readers on a round input.
* `BB1Machine.listToNat_modS`, …, `BB1Machine.listToNat_invS` — the arithmetic in `Z_p`.
* `BB1Machine.listToNat_pS`, `mulGS_ofFn`, `powGS_ofFn`, `mulT_ofFn`, `memT_ofFn`,
  `memT_headD` — the group operations on encodings.
* `BB1Machine.uS_of_blkS` — the drawn exponent's numeral.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
  `B` in the proof of Theorem 4.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 43.2, the extended Euclidean algorithm. Context only: §2.8, Theorem 52.3, the
  discrete-log collection, whose proof remarks that its domain `Z_q` is easy to sample; it does
  not give the bounded sampler or its bound, which are the library's `Candidates.sampleBelowL`
  and `Candidates.statClose_sampleBelowL`, `Cryptography/Candidates/DiscreteLog.lean`.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability TCSlib.Cryptography.NumberTheory
  TCSlib.Cryptography.Candidates

namespace BB1Machine

noncomputable section

variable (G : BilinearGen) (ℓ : PolyExpr) (O : G.Ops)

/-! ### Lengths -/

/-- The width `aWidth G = wG + 1` of the numeral of `α_1` in the state. -/
def aWidth : PolyExpr := G.wG.add (.const 1)

/-- `(aWidth G).eval κ = wG(κ) + 1`. -/
theorem aWidth_eval (κ : ℕ) : (aWidth G).eval κ = G.wG.eval κ + 1 := by
  rw [aWidth, PolyExpr.eval_add, PolyExpr.eval_const]

/-- The block length `nn G = n · n` of one exponent's coins, `n = blockLen G`. -/
def nn : PolyExpr := (blockLen G).mul (blockLen G)

/-- `(nn G).eval κ = n · n`. -/
theorem nn_eval (κ : ℕ) : (nn G).eval κ = (blockLen G).eval κ * (blockLen G).eval κ := by
  rw [nn, PolyExpr.eval_mul]

/-! ### Reading the round input `⟨⟨1^κ, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` -/

/-- The parameter `1^κ` of the round input: `rU w = pairFstD (pairFstD w)`. -/
def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
/-- The reduction input `z`: `rZ w = pairFstD (pairSndD (pairFstD w))`. -/
def rZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))
/-- The seed `ω`: `rW w = pairSndD (pairSndD (pairFstD w))`. -/
def rW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
/-- The state `s`: `rS w = pairFstD (pairSndD w)`. -/
def rS (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- The oracle index `1^i`: `rI w = pairFstD (pairSndD (pairSndD w))`. -/
def rI (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD w))
/-- The query `x`: `rX w = pairSndD (pairSndD (pairSndD w))`. -/
def rX (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- The description `d` of `z = ⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩`: `zD w = pairFstD (rZ w)`. -/
def zD (w : List Bool) : List Bool := pairFstD (rZ w)
/-- The word of `g`: `zG w = pairFstD (pairSndD (rZ w))`. -/
def zG (w : List Bool) : List Bool := pairFstD (pairSndD (rZ w))
/-- The word of `X`: `zX w = pairFstD (pairSndD² (rZ w))`. -/
def zX (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (rZ w)))
/-- The word of `Y`: `zY w = pairFstD (pairSndD³ (rZ w))`. -/
def zY (w : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD (rZ w))))
/-- The word of `Z`: `zZ w = pairFstD (pairSndD⁴ (rZ w))`. -/
def zZ (w : List Bool) : List Bool :=
  pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w)))))
/-- The word of `T`: `zT w = pairSndD⁵ (rZ w)`. -/
def zT (w : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w)))))

/-- The counter `1^j` of the state `⟨1^j, ⟨o_1, o_2⟩⟩`: `sJ w = pairFstD (rS w)`. -/
def sJ (w : List Bool) : List Bool := pairFstD (rS w)
/-- The commitment `o_1`: `sO1 w = pairFstD (pairSndD (rS w))`. -/
def sO1 (w : List Bool) : List Bool := pairFstD (pairSndD (rS w))
/-- The challenge record `o_2` followed by the padding: `sR w = pairSndD (pairSndD (rS w))`. -/
def sR (w : List Bool) : List Bool := pairSndD (pairSndD (rS w))
/-- Whether an identity is committed: `sCom w = [o_1 ≠ []]`. -/
def sCom (w : List Bool) : Bool := !decide (sO1 w = [])
/-- Whether a challenge is recorded, the first bit of `o_2`: `sChal w = (sR w).headD false`. -/
def sChal (w : List Bool) : Bool := (sR w).headD false
/-- The recorded challenge `C` of `o_2 = 1 ‖ C`: the `ctLen(κ)` bits after the first. -/
def sC (w : List Bool) : List Bool :=
  ((sR w).drop 1).take ((bb1Scheme G ℓ).ctLen.eval (rU w).length)
/-- The challenge record without its padding: `1 :: sC w` if a challenge is recorded, else `[]`. -/
def sO2 (w : List Bool) : List Bool := if sChal w then true :: sC G ℓ w else []
/-- The committed identity: `kT w = pairFstD (sO1 w)`. -/
def kT (w : List Bool) : List Bool := pairFstD (sO1 w)
/-- The numeral of the committed `α_1`: `kA w = pairSndD (sO1 w)`. -/
def kA (w : List Bool) : List Bool := pairSndD (sO1 w)

/-! ### Arithmetic modulo `p` and in the groups -/

/-- The numeral of the order `p`: `pS w = orderStr (zD w)`. -/
def pS (w : List Bool) : List Bool := O.orderStr (zD w)
/-- `a mod p`: `modS w a = pairSndD (divModStr ⟨a, pS w⟩)`. -/
def modS (w a : List Bool) : List Bool := pairSndD (divModStr (pairEncode a (pS G O w)))
/-- The residue of `−a`: `negS w a = modS w (subStr ⟨pS w, modS w a⟩)`. -/
def negS (w a : List Bool) : List Bool :=
  modS G O w (subStr (pairEncode (pS G O w) (modS G O w a)))
/-- `(a + c) mod p`: `addS w a c = modS w (addStr ⟨a, c⟩)`. -/
def addS (w a c : List Bool) : List Bool := modS G O w (addStr (pairEncode a c))
/-- `(a · c) mod p`: `mulS w a c = modS w (mulStr ⟨a, c⟩)`. -/
def mulS (w a c : List Bool) : List Bool := modS G O w (mulStr (pairEncode a c))
/-- The inverse of `a` modulo `p` (`0` for `a ≡ 0`): `invS w a = pairSndD (xgcdStr ⟨a, pS w⟩)`. -/
def invS (w a : List Bool) : List Bool := pairSndD (xgcdStr (pairEncode a (pS G O w)))
/-- The product `x · y` in `G`: `mulGS w x y = mulG ⟨zD w, ⟨x, y⟩⟩`. -/
def mulGS (w x y : List Bool) : List Bool := O.mulG (pairEncode (zD w) (pairEncode x y))
/-- The power `x^e` in `G`: `powGS w x e = powG ⟨zD w, ⟨x, e⟩⟩`. -/
def powGS (w x e : List Bool) : List Bool := O.powG (pairEncode (zD w) (pairEncode x e))

/-! ### The exponent of the query -/

/-- The block of `n · n` seed bits of the `j`-th query:
`blkS w = ((rW w).drop (j · n²)).take n²` with `j = |sJ w|`. -/
def blkS (w : List Bool) : List Bool :=
  ((rW w).drop ((sJ w).length * (nn G).eval (rU w).length)).take ((nn G).eval (rU w).length)

/-- The exponent drawn from the block, as a `(wG(κ) + 1)`-bit numeral:
`uS w = ⟦(sampleBelowL p (Nat.size p) n n (blkS w)).getD 0⟧_{wG+1}`, `p = ⟦pS w⟧`. -/
def uS (w : List Bool) : List Bool :=
  natToList ((aWidth G).eval (rU w).length)
    ((sampleBelowL (listToNat (pS G O w)) (Nat.size (listToNat (pS G O w)))
      ((blockLen G).eval (rU w).length) ((blockLen G).eval (rU w).length) (blkS G w)).getD 0)

/-! ### The readers' equations -/

/-- `rU w = pairFstD (pairFstD w)`. -/
theorem rU_eq (w : List Bool) : rU w = pairFstD (pairFstD w) := rfl
/-- `rZ w = pairFstD (pairSndD (pairFstD w))`. -/
theorem rZ_eq (w : List Bool) : rZ w = pairFstD (pairSndD (pairFstD w)) := rfl
/-- `rW w = pairSndD (pairSndD (pairFstD w))`. -/
theorem rW_eq (w : List Bool) : rW w = pairSndD (pairSndD (pairFstD w)) := rfl
/-- `rS w = pairFstD (pairSndD w)`. -/
theorem rS_eq (w : List Bool) : rS w = pairFstD (pairSndD w) := rfl
/-- `rI w = pairFstD (pairSndD (pairSndD w))`. -/
theorem rI_eq (w : List Bool) : rI w = pairFstD (pairSndD (pairSndD w)) := rfl
/-- `rX w = pairSndD (pairSndD (pairSndD w))`. -/
theorem rX_eq (w : List Bool) : rX w = pairSndD (pairSndD (pairSndD w)) := rfl
/-- `zD w = pairFstD (rZ w)`. -/
theorem zD_eq (w : List Bool) : zD w = pairFstD (rZ w) := rfl
/-- `zG w = pairFstD (pairSndD (rZ w))`. -/
theorem zG_eq (w : List Bool) : zG w = pairFstD (pairSndD (rZ w)) := rfl
/-- `zX w = pairFstD (pairSndD (pairSndD (rZ w)))`. -/
theorem zX_eq (w : List Bool) : zX w = pairFstD (pairSndD (pairSndD (rZ w))) := rfl
/-- `zY w = pairFstD (pairSndD (pairSndD (pairSndD (rZ w))))`. -/
theorem zY_eq (w : List Bool) : zY w = pairFstD (pairSndD (pairSndD (pairSndD (rZ w)))) := rfl
/-- `zZ w = pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w)))))`. -/
theorem zZ_eq (w : List Bool) :
    zZ w = pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w))))) := rfl
/-- `zT w = pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w)))))`. -/
theorem zT_eq (w : List Bool) :
    zT w = pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (rZ w))))) := rfl
/-- `sJ w = pairFstD (rS w)`. -/
theorem sJ_eq (w : List Bool) : sJ w = pairFstD (rS w) := rfl
/-- `sO1 w = pairFstD (pairSndD (rS w))`. -/
theorem sO1_eq (w : List Bool) : sO1 w = pairFstD (pairSndD (rS w)) := rfl
/-- `sR w = pairSndD (pairSndD (rS w))`. -/
theorem sR_eq (w : List Bool) : sR w = pairSndD (pairSndD (rS w)) := rfl
/-- `sCom w = !decide (sO1 w = [])`. -/
theorem sCom_eq (w : List Bool) : sCom w = !decide (sO1 w = []) := rfl
/-- `sChal w = (sR w).headD false`. -/
theorem sChal_eq (w : List Bool) : sChal w = (sR w).headD false := rfl
/-- `sC G ℓ w = ((sR w).drop 1).take (ctLen.eval |rU w|)`. -/
theorem sC_eq (w : List Bool) :
    sC G ℓ w = ((sR w).drop 1).take ((bb1Scheme G ℓ).ctLen.eval (rU w).length) := rfl
/-- `sO2 G ℓ w = if sChal w then true :: sC G ℓ w else []`. -/
theorem sO2_eq (w : List Bool) : sO2 G ℓ w = if sChal w then true :: sC G ℓ w else [] := rfl
/-- `kT w = pairFstD (sO1 w)`. -/
theorem kT_eq (w : List Bool) : kT w = pairFstD (sO1 w) := rfl
/-- `kA w = pairSndD (sO1 w)`. -/
theorem kA_eq (w : List Bool) : kA w = pairSndD (sO1 w) := rfl
/-- `pS G O w = orderStr (zD w)`. -/
theorem pS_eq (w : List Bool) : pS G O w = O.orderStr (zD w) := rfl
/-- `modS G O w a = pairSndD (divModStr ⟨a, pS G O w⟩)`. -/
theorem modS_eq (w a : List Bool) :
    modS G O w a = pairSndD (divModStr (pairEncode a (pS G O w))) := rfl
/-- `negS G O w a = modS G O w (subStr ⟨pS G O w, modS G O w a⟩)`. -/
theorem negS_eq (w a : List Bool) :
    negS G O w a = modS G O w (subStr (pairEncode (pS G O w) (modS G O w a))) := rfl
/-- `addS G O w a c = modS G O w (addStr ⟨a, c⟩)`. -/
theorem addS_eq (w a c : List Bool) : addS G O w a c = modS G O w (addStr (pairEncode a c)) :=
  rfl
/-- `mulS G O w a c = modS G O w (mulStr ⟨a, c⟩)`. -/
theorem mulS_eq (w a c : List Bool) : mulS G O w a c = modS G O w (mulStr (pairEncode a c)) :=
  rfl
/-- `invS G O w a = pairSndD (xgcdStr ⟨a, pS G O w⟩)`. -/
theorem invS_eq (w a : List Bool) :
    invS G O w a = pairSndD (xgcdStr (pairEncode a (pS G O w))) := rfl
/-- `mulGS G O w x y = mulG ⟨zD w, ⟨x, y⟩⟩`. -/
theorem mulGS_eq (w x y : List Bool) :
    mulGS G O w x y = O.mulG (pairEncode (zD w) (pairEncode x y)) := rfl
/-- `powGS G O w x e = powG ⟨zD w, ⟨x, e⟩⟩`. -/
theorem powGS_eq (w x e : List Bool) :
    powGS G O w x e = O.powG (pairEncode (zD w) (pairEncode x e)) := rfl
/-- `blkS G w = ((rW w).drop (|sJ w| · n²)).take n²`. -/
theorem blkS_eq (w : List Bool) :
    blkS G w = ((rW w).drop ((sJ w).length * (nn G).eval (rU w).length)).take
      ((nn G).eval (rU w).length) := rfl
/-- `uS G O w = ⟦(sampleBelowL p (Nat.size p) n n (blkS G w)).getD 0⟧_{wG+1}`. -/
theorem uS_eq (w : List Bool) :
    uS G O w = natToList ((aWidth G).eval (rU w).length)
      ((sampleBelowL (listToNat (pS G O w)) (Nat.size (listToNat (pS G O w)))
        ((blockLen G).eval (rU w).length) ((blockLen G).eval (rU w).length) (blkS G w)).getD 0) :=
  rfl

/-! ### Polynomial time -/

section Poly

/-- `rU` is polynomial-time (two first projections). -/
theorem poly_rU : PolyTimeComputable rU :=
  polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
/-- `rZ` is polynomial-time. -/
theorem poly_rZ : PolyTimeComputable rZ :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
/-- `rW` is polynomial-time. -/
theorem poly_rW : PolyTimeComputable rW :=
  polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD)
/-- `rS` is polynomial-time. -/
theorem poly_rS : PolyTimeComputable rS :=
  polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
/-- `rI` is polynomial-time. -/
theorem poly_rI : PolyTimeComputable rI :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
/-- `rX` is polynomial-time. -/
theorem poly_rX : PolyTimeComputable rX :=
  polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
/-- `zD` is polynomial-time. -/
theorem poly_zD : PolyTimeComputable zD := polyTimeComputable_pairFstD.comp' poly_rZ
/-- `zG` is polynomial-time. -/
theorem poly_zG : PolyTimeComputable zG :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' poly_rZ)
/-- `zX` is polynomial-time. -/
theorem poly_zX : PolyTimeComputable zX :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' poly_rZ))
/-- `zY` is polynomial-time. -/
theorem poly_zY : PolyTimeComputable zY :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' poly_rZ)))
/-- `zZ` is polynomial-time. -/
theorem poly_zZ : PolyTimeComputable zZ :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' poly_rZ))))
/-- `zT` is polynomial-time. -/
theorem poly_zT : PolyTimeComputable zT :=
  polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' poly_rZ))))
/-- `sJ` is polynomial-time. -/
theorem poly_sJ : PolyTimeComputable sJ := polyTimeComputable_pairFstD.comp' poly_rS
/-- `sO1` is polynomial-time. -/
theorem poly_sO1 : PolyTimeComputable sO1 :=
  polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' poly_rS)
/-- `sR` is polynomial-time. -/
theorem poly_sR : PolyTimeComputable sR :=
  polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' poly_rS)
/-- `w ↦ [sCom w]` is polynomial-time (`isNil`, then `not`). -/
theorem poly_sCom : PolyTimeComputable fun w => [sCom w] :=
  polyTimeComputable_not (polyTimeComputable_isNil.comp' poly_sO1)
/-- `w ↦ [sChal w]` is polynomial-time (`headD`). -/
theorem poly_sChal : PolyTimeComputable fun w => [sChal w] :=
  polyTimeComputable_headD.comp' poly_sR
/-- `sC G ℓ` is polynomial-time (`pairTakePoly ctLen` of `⟨rU w, (sR w).tail⟩`). -/
theorem poly_sC : PolyTimeComputable (sC G ℓ) :=
  ((polyTimeComputable_pairTakePoly (bb1Scheme G ℓ).ctLen).comp'
    (poly_rU.pairEncode (polyTimeComputable_tail.comp' poly_sR))).congr fun w => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]; rfl
/-- `sO2 G ℓ` is polynomial-time (a branch on `sChal`). -/
theorem poly_sO2 : PolyTimeComputable (sO2 G ℓ) :=
  (polyTimeComputable_ite poly_sChal ((polyTimeComputable_const [true]).append (poly_sC G ℓ))
    (polyTimeComputable_const [])).congr fun w => by
      simp only [sO2, List.singleton_append]
/-- `kT` is polynomial-time. -/
theorem poly_kT : PolyTimeComputable kT := polyTimeComputable_pairFstD.comp' poly_sO1
/-- `kA` is polynomial-time. -/
theorem poly_kA : PolyTimeComputable kA := polyTimeComputable_pairSndD.comp' poly_sO1

/-- `pS G O` is polynomial-time (`orderStr_poly`). -/
theorem poly_pS : PolyTimeComputable (pS G O) := O.orderStr_poly.comp' poly_zD

/-- `w ↦ modS G O w (a w)` is polynomial-time for polynomial-time `a` (`H.divMod`). -/
theorem poly_modS (H : ArithmeticFP) {a : List Bool → List Bool} (ha : PolyTimeComputable a) :
    PolyTimeComputable fun w => modS G O w (a w) :=
  polyTimeComputable_pairSndD.comp' (H.divMod.comp' (ha.pairEncode (poly_pS G O)))
/-- `w ↦ negS G O w (a w)` is polynomial-time for polynomial-time `a` (`H.sub`). -/
theorem poly_negS (H : ArithmeticFP) {a : List Bool → List Bool} (ha : PolyTimeComputable a) :
    PolyTimeComputable fun w => negS G O w (a w) :=
  poly_modS G O H (H.sub.comp' ((poly_pS G O).pairEncode (poly_modS G O H ha)))
/-- `w ↦ addS G O w (a w) (c w)` is polynomial-time for polynomial-time `a`, `c`. -/
theorem poly_addS (H : ArithmeticFP) {a c : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hc : PolyTimeComputable c) : PolyTimeComputable fun w => addS G O w (a w) (c w) :=
  poly_modS G O H (H.add.comp' (ha.pairEncode hc))
/-- `w ↦ mulS G O w (a w) (c w)` is polynomial-time for polynomial-time `a`, `c`. -/
theorem poly_mulS (H : ArithmeticFP) {a c : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hc : PolyTimeComputable c) : PolyTimeComputable fun w => mulS G O w (a w) (c w) :=
  poly_modS G O H (H.mul.comp' (ha.pairEncode hc))
/-- `w ↦ invS G O w (a w)` is polynomial-time for polynomial-time `a` (`H.xgcd`). -/
theorem poly_invS (H : ArithmeticFP) {a : List Bool → List Bool} (ha : PolyTimeComputable a) :
    PolyTimeComputable fun w => invS G O w (a w) :=
  polyTimeComputable_pairSndD.comp' (H.xgcd.comp' (ha.pairEncode (poly_pS G O)))
/-- `w ↦ mulGS G O w (x w) (y w)` is polynomial-time for polynomial-time `x`, `y`. -/
theorem poly_mulGS {x y : List Bool → List Bool} (hx : PolyTimeComputable x)
    (hy : PolyTimeComputable y) : PolyTimeComputable fun w => mulGS G O w (x w) (y w) :=
  O.mulG_poly.comp' (poly_zD.pairEncode (hx.pairEncode hy))
/-- `w ↦ powGS G O w (x w) (e w)` is polynomial-time for polynomial-time `x`, `e`. -/
theorem poly_powGS {x e : List Bool → List Bool} (hx : PolyTimeComputable x)
    (he : PolyTimeComputable e) : PolyTimeComputable fun w => powGS G O w (x w) (e w) :=
  O.powG_poly.comp' (poly_zD.pairEncode (hx.pairEncode he))

/-- `blkS G` is polynomial-time: the offset `1^{|sJ w| · n²}`
(`OneWay.polyTimeComputable_unaryMulPair`), a drop by its length and a take of `n²` bits. -/
theorem poly_blkS : PolyTimeComputable (blkS G) := by
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((sJ w).length * (nn G).eval (rU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp'
      (poly_sJ.pairEncode ((polyTimeComputable_unaryPoly (nn G)).comp' poly_rU))).congr fun w => by
        simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  have hDrop : PolyTimeComputable fun w =>
      (rW w).drop ((sJ w).length * (nn G).eval (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp' (hOff.pairEncode poly_rW)).congr fun w => by
      simp only [PrefixByLength.drop_def, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate]
  exact ((polyTimeComputable_pairTakePoly (nn G)).comp' (poly_rU.pairEncode hDrop)).congr
    fun w => by simp only [pairFstD_pairEncode, pairSndD_pairEncode]; rfl

/-- `uS G O` is polynomial-time.

**Proof sketch.** Apply the block-rejection host `Candidates.polyTimeComputable_rejectBlocksL`
with the test `v < p` (`H.le`), the width word `sizeStr p` (`H.size`) and `n` blocks of `n`
bits read from `blkS w`: its output `g w` is empty when the sampler fails, and otherwise its
tail, of at most `|sizeStr p|` bits, reads as the accepted value
(`sampleBelowL_eq_rejectBlocksL`). Take the tail, then normalize the width by
`(⟦0⟧_W ‖ v).drop |v| = ⟦⟦v⟧⟧_W` (`natToList_zero_append_drop`, with `⟦0⟧_W = subStr ⟨1^W, 1^W⟩`
and `W = wG + 1`), as in `Candidates.polyTimeComputable_expSampleRaw`; on a failure the tail is
empty and reads as `0`, the fallback value. -/
theorem poly_uS (H : ArithmeticFP) : PolyTimeComputable (uS G O) := by
  have hN : PolyTimeComputable fun w => List.replicate ((blockLen G).eval (rU w).length) true :=
    (polyTimeComputable_unaryPoly (blockLen G)).comp' poly_rU
  obtain ⟨g, hg, hs⟩ := polyTimeComputable_rejectBlocksL (fun a v => v < a)
    (acc := fun x => !decide (listToNat (pairFstD x) ≤ listToNat (pairSndD x)))
    (polyTimeComputable_not (H.le_poly polyTimeComputable_pairFstD polyTimeComputable_pairSndD))
    (fun w c => by
      dsimp only
      rw [pairFstD_pairEncode, pairSndD_pairEncode, ← decide_not, decide_eq_decide, Nat.not_le])
    (poly_pS G O) (H.size.comp' (poly_pS G O)) hN hN (poly_blkS G)
  have hb : PolyTimeComputable fun w => (g w).tail :=
    (PolyTimeComputable.comp' polyTimeComputable_tail hg).congr fun w => List.drop_one
  have hW : PolyTimeComputable fun w => List.replicate ((aWidth G).eval (rU w).length) true :=
    (polyTimeComputable_unaryPoly (aWidth G)).comp' poly_rU
  have hz := H.sub.comp' (hW.pairEncode hW)
  have hq := (polyTimeComputable_pairDropPoly .var).comp' (hb.pairEncode (hz.append hb))
  refine hq.congr fun w => ?_
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var, subStr_self,
    List.length_replicate]
  rw [natToList_zero_append_drop, uS, sampleBelowL_eq_rejectBlocksL]
  have h2 := (hs w).2
  rw [length_sizeStr, List.length_replicate] at h2
  rw [h2]
  split_ifs with he
  · rw [he, List.tail_nil, listToNat_nil]
    rfl
  · rfl

end Poly

/-! ### Reading the round input -/

section Fields

variable {κ : ℕ} {z W S X : List Bool} {i : Fin 3}

/-- `rU (input κ z ω s i x) = 1^κ`. -/
theorem rU_input : rU (PolyHandler.input κ z W S i X) = List.replicate κ true := by
  rw [PolyHandler.input_eq, rU, pairFstD_pairEncode, pairFstD_pairEncode]
/-- `rZ (input κ z ω s i x) = z`. -/
theorem rZ_input : rZ (PolyHandler.input κ z W S i X) = z := by
  rw [PolyHandler.input_eq, rZ, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode]
/-- `rW (input κ z ω s i x) = ω`. -/
theorem rW_input : rW (PolyHandler.input κ z W S i X) = W := by
  rw [PolyHandler.input_eq, rW, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
/-- `rS (input κ z ω s i x) = s`. -/
theorem rS_input : rS (PolyHandler.input κ z W S i X) = S := by
  rw [PolyHandler.input_eq, rS, pairSndD_pairEncode, pairFstD_pairEncode]
/-- `rI (input κ z ω s i x) = 1^i`. -/
theorem rI_input : rI (PolyHandler.input κ z W S i X) = List.replicate i true := by
  rw [PolyHandler.input_eq, rI, pairSndD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode]
/-- `rX (input κ z ω s i x) = x`. -/
theorem rX_input : rX (PolyHandler.input κ z W S i X) = X := by
  rw [PolyHandler.input_eq, rX, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]

end Fields

section Tuple

variable {w : List Bool} {wG wT : ℕ} {B : BilinearGroup wG wT} {d : List Bool}
  {g X Y Z : B.G} {T : B.GT}

/-- `zD w = d` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zD_of (h : rZ w = tupleStr B d g X Y Z T) : zD w = d := by
  rw [zD, h, tupleStr_eq, pairFstD_pairEncode]
/-- `zG w = ⟦g⟧` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zG_of (h : rZ w = tupleStr B d g X Y Z T) : zG w = List.ofFn (B.encG g) := by
  rw [zG, h, tupleStr_eq, pairSndD_pairEncode, pairFstD_pairEncode]
/-- `zX w = ⟦X⟧` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zX_of (h : rZ w = tupleStr B d g X Y Z T) : zX w = List.ofFn (B.encG X) := by
  rw [zX, h, tupleStr_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode]
/-- `zY w = ⟦Y⟧` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zY_of (h : rZ w = tupleStr B d g X Y Z T) : zY w = List.ofFn (B.encG Y) := by
  rw [zY, h, tupleStr_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
/-- `zZ w = ⟦Z⟧` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zZ_of (h : rZ w = tupleStr B d g X Y Z T) : zZ w = List.ofFn (B.encG Z) := by
  rw [zZ, h, tupleStr_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode,
    pairSndD_pairEncode, pairFstD_pairEncode]
/-- `zT w = ⟦T⟧` when `rZ w = tupleStr B d g X Y Z T`. -/
theorem zT_of (h : rZ w = tupleStr B d g X Y Z T) : zT w = List.ofFn (B.encT T) := by
  rw [zT, h, tupleStr_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode,
    pairSndD_pairEncode, pairSndD_pairEncode]

end Tuple

/-! ### Arithmetic modulo `p` on numerals -/

section Arith

variable {w : List Bool} {p : ℕ} [NeZero p]

omit [NeZero p] in
/-- The order read from `pS` fits its numeral: `p < 2^{|pS w|}`. -/
theorem pS_lt (hp : listToNat (pS G O w) = p) : p < 2 ^ (pS G O w).length :=
  hp ▸ listToNat_lt_two_pow _

/-- `⟦a mod p⟧ = (a : Z_p).val`. -/
theorem listToNat_modS (hp : listToNat (pS G O w) = p) (a : List Bool) :
    listToNat (modS G O w a) = ((listToNat a : ZMod p)).val := by
  rw [modS, divModStr_pairEncode, pairSndD_pairEncode, hp, ZMod.val_natCast]
  exact listToNat_natToList ((Nat.mod_lt _ (NeZero.pos p)).trans (pS_lt G O hp))

/-- `⟦−a mod p⟧ = (−(a : Z_p)).val`. -/
theorem listToNat_negS (hp : listToNat (pS G O w) = p) (a : List Bool) :
    listToNat (negS G O w a) = (-(listToNat a : ZMod p)).val := by
  rw [negS, listToNat_modS G O hp, listToNat_subStr, hp, listToNat_modS G O hp, ZMod.neg_val',
    ZMod.val_natCast]

/-- `⟦(a + c) mod p⟧ = ((a : Z_p) + c).val`. -/
theorem listToNat_addS (hp : listToNat (pS G O w) = p) (a c : List Bool) :
    listToNat (addS G O w a c) = ((listToNat a : ZMod p) + (listToNat c : ZMod p)).val := by
  rw [addS, listToNat_modS G O hp, listToNat_addStr, Nat.cast_add]

/-- `⟦(a · c) mod p⟧ = ((a : Z_p) · c).val`. -/
theorem listToNat_mulS (hp : listToNat (pS G O w) = p) (a c : List Bool) :
    listToNat (mulS G O w a c) = ((listToNat a : ZMod p) * (listToNat c : ZMod p)).val := by
  rw [mulS, listToNat_modS G O hp, listToNat_mulStr, Nat.cast_mul]

/-- `⟦a⁻¹ mod p⟧ = ((a : Z_p)⁻¹).val` (the extended Euclidean algorithm; `0⁻¹ = 0`). -/
theorem listToNat_invS (hp : listToNat (pS G O w) = p) (a : List Bool) :
    listToNat (invS G O w a) = ((listToNat a : ZMod p)⁻¹).val := by
  rw [invS, xgcdStr_pairEncode, pairSndD_pairEncode, hp]
  exact listToNat_natToList ((ZMod.val_lt _).trans (pS_lt G O hp))

end Arith

/-! ### Group operations on encodings -/

section Group

variable {w : List Bool} {κ : ℕ} {r : G.gen.Coins κ}

/-- `⟦pS⟧ = p` on the generated description. -/
theorem listToNat_pS (hD : zD w = G.desc κ r) :
    listToNat (pS G O w) = (G.group κ (G.desc κ r)).order := by
  have h := O.orderStr_spec κ r
  rw [BilinearGen.inst_eq] at h
  rw [pS, hD]
  exact h

/-- `mulG` on encodings: `⟦x⟧ · ⟦y⟧ = ⟦x · y⟧`. -/
theorem mulGS_ofFn (hD : zD w = G.desc κ r) (x y : (G.group κ (G.desc κ r)).G) :
    mulGS G O w (List.ofFn ((G.group κ (G.desc κ r)).encG x))
      (List.ofFn ((G.group κ (G.desc κ r)).encG y)) =
      List.ofFn ((G.group κ (G.desc κ r)).encG (x * y)) := by
  have h := O.mulG_spec κ r
  rw [BilinearGen.inst_eq] at h
  rw [mulGS, hD]
  exact h x y

/-- `powG` on encodings: `⟦x⟧^e = ⟦x^{⟦e⟧}⟧`. -/
theorem powGS_ofFn (hD : zD w = G.desc κ r) (x : (G.group κ (G.desc κ r)).G)
    (e : List Bool) :
    powGS G O w (List.ofFn ((G.group κ (G.desc κ r)).encG x)) e =
      List.ofFn ((G.group κ (G.desc κ r)).encG (x ^ listToNat e)) := by
  have h := O.powG_spec κ r
  rw [BilinearGen.inst_eq] at h
  rw [powGS, hD]
  exact h x e

/-- `mulT` on encodings: `⟦u⟧ · ⟦v⟧ = ⟦u · v⟧` in `G_T`. -/
theorem mulT_ofFn (hD : zD w = G.desc κ r) (u v : (G.group κ (G.desc κ r)).GT) :
    O.mulT (pairEncode (zD w) (pairEncode (List.ofFn ((G.group κ (G.desc κ r)).encT u))
      (List.ofFn ((G.group κ (G.desc κ r)).encT v)))) =
      List.ofFn ((G.group κ (G.desc κ r)).encT (u * v)) := by
  have h := O.mulT_spec κ r
  rw [BilinearGen.inst_eq] at h
  rw [hD]
  exact h u v

/-- `memT` on encodings: `[w encodes an element of G_T]`. -/
theorem memT_ofFn (hD : zD w = G.desc κ r) (m : Fin (G.wT.eval κ) → Bool) :
    O.memT (pairEncode (zD w) (List.ofFn m)) =
      [decide (∃ u, (G.group κ (G.desc κ r)).encT u = m)] := by
  have h := O.memT_spec κ r
  rw [BilinearGen.inst_eq] at h
  rw [hD]
  exact h m

/-- The membership test on a `wT`-bit word: `(memT ⟨d, l⟩).headD false = [l encodes some u]`. -/
theorem memT_headD (hD : zD w = G.desc κ r) (l : List Bool) (hl : l.length = G.wT.eval κ) :
    (O.memT (pairEncode (zD w) l)).headD false =
      decide (∃ u, List.ofFn ((G.group κ (G.desc κ r)).encT u) = l) := by
  have h := memT_ofFn G O hD (padFin _ l)
  rw [ofFn_padFin_of_length hl] at h
  rw [h, List.headD_cons, decide_eq_decide]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [hu, ofFn_padFin_of_length hl]⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [← hu, padFin_ofFn]⟩

end Group

/-! ### The order and the identities -/

section Order

variable {κ : ℕ}

/-- The width of `α_1`'s numeral is `wG + 1`, and the order is below `2^{wG + 1}`. -/
theorem order_lt_aWidth (κ : ℕ) (d : List Bool) :
    (G.group κ d).order < 2 ^ (aWidth G).eval κ := by
  rw [aWidth, PolyExpr.eval_add, PolyExpr.eval_const, pow_succ]
  have := order_le_two_pow G κ d
  have h2 : 0 < 2 ^ G.wG.eval κ := Nat.two_pow_pos _
  omega

/-- The numeral of a residue at width `wG + 1` reads back as its value. -/
theorem listToNat_natToList_val {d : List Bool} (v : ZMod (G.group κ d).order) :
    listToNat (natToList ((aWidth G).eval κ) v.val) = v.val :=
  listToNat_natToList ((ZMod.val_lt v).trans (order_lt_aWidth G κ d))

/-- An identity read in `Z_p` is its numeral's residue:
`idToZ (padFin _ ⟦x⟧) = (⟦x⟧ : Z_p)`. -/
theorem idToZ_padFin {d : List Bool} {e : ℕ} (x : Fin e → Bool)
    (h : e = (bb1Scheme G ℓ).idLen.eval κ) :
    BB1.idToZ (G.group κ d) (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) =
      ((listToNat (List.ofFn x) : ℕ) : ZMod (G.group κ d).order) := by
  rw [BB1.idToZ_eq, NumberTheory.bitsToNat_eq_listToNat,
    ofFn_padFin_of_length (by rw [List.length_ofFn, h])]

end Order

/-! ### The drawn exponent -/

/-- **The drawn exponent's numeral**: if the block of the query is `⟦v⟧`, then
`uS w = ⟦(draw G κ d v).val⟧_{wG+1}` (`draw_eq`; a drawn value is below `p`). -/
theorem uS_of_blkS {w : List Bool} {κ : ℕ} {r : G.gen.Coins κ} (hU : (rU w).length = κ)
    (hD : zD w = G.desc κ r) (v : Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool)
    (hv : blkS G w = List.ofFn v) :
    uS G O w = natToList ((aWidth G).eval κ) (draw G κ (G.desc κ r) v).val := by
  have hp := listToNat_pS G O hD
  rw [uS, hU, hp, hv, draw_eq, ZMod.val_natCast, Nat.mod_eq_of_lt]
  generalize hs : sampleBelowL _ _ _ _ _ = o
  rcases o with _ | u
  · exact (G.group κ (G.desc κ r)).order_prime.pos
  · exact sampleBelowL_lt hs

end

end BB1Machine

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine/Handler.lean (Lean, at 98cb0e521a94e94c304c78348fb5d3033435a3ed) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Words
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator as a polynomial-time handler

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (step 3 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): the paper's algorithm `B` answering the
adversary's `Init`, `KeyGen` and `Challenge` queries, as a polynomial-time handler
(`Games.PolyHandler`) of the handler theorem T1 (`Games.exists_handlerMachine`). It works on
the encodings only: group operations by the contract `Pairing.BilinearGen.Ops`, exponent
arithmetic modulo `p` by the arithmetic bundle `Candidates.ArithmeticFP`, and each exponent
`α_1`, `r` drawn from the next block of `n · n` seed bits by the rejection sampler of
`BonehBoyenMachine/Draws.lean`. The string functions it is assembled from (readers of the round
input, arithmetic modulo `p`, the group operations, the drawn exponent) are those of
`BonehBoyenMachine/Words.lean`.

**The run.** The reduction input is the Decision BDH string `⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩` and the
seed `ω` holds `q(κ)` blocks of `n · n` bits. The state is `⟨1^j, ⟨o_1, o_2⟩⟩` padded to a fixed
length: `j` queries answered so far, `o_1 = ⟨ID*, α_1⟩` (the committed identity and `α_1` as a
`(wG(κ) + 1)`-bit numeral) or empty, and `o_2 = 1 ‖ C` (the recorded challenge) or empty. The
`j`-th query reads its exponent from block `j`. Negation and differences of residues are
computed with truncated subtraction and division with remainder, and inverses with the extended
Euclidean algorithm, whose inverse of `0` is `0`, as in `Z_p`.

**Its meaning.** On the encoding of a state of the simulator, one query to the handler is one
query to `drawStep` with the exponent read from the seed (`handler_impl_stEnc`), so the whole
run is the run of `drawStep` with exponents read from a tape, through the encoding of the states
(`simulate_handler`).

## Main definitions

* `BB1Machine.handler` — the handler.
* `BB1Machine.seedBlocks` — the seed as `q(κ)` blocks of `n · n` bits.

## Main results

* `BB1Machine.handler_advInput`, `BB1Machine.handler_result` — the adversary's input and the
  reduction's output.
* `BB1Machine.seedBlocks_window` — block `j` of the seed is its `j`-th window of `n · n` bits.
* `BB1Machine.simulate_handler` — the handler's run is the run of `drawStep` with exponents
  drawn from the seed blocks.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
  `B` in the proof of Theorem 4.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 43.2, the extended Euclidean algorithm. Context only: §2.8, Theorem 52.3, the
  discrete-log collection, whose proof remarks that its domain `Z_q` is easy to sample; it does
  not give the bounded sampler or its bound, which are the library's `Candidates.sampleBelowL`
  and `Candidates.statClose_sampleBelowL`, `Cryptography/Candidates/DiscreteLog.lean`.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability TCSlib.Cryptography.NumberTheory
  TCSlib.Cryptography.Candidates

namespace BB1Machine

noncomputable section

variable (G : BilinearGen) (ℓ : PolyExpr) (O : G.Ops) (b : Bool) (q : PolyExpr)

/-! ### Lengths -/

/-- The state length `2q + 4ℓ + 4wG + wT + 11`, room for `⟨1^j, ⟨⟨ID*, α_1⟩, 1 ‖ C⟩⟩`, `j ≤ q`. -/
private def stLen : PolyExpr :=
  ((((q.mul (.const 2)).add (ℓ.mul (.const 4))).add (G.wG.mul (.const 4))).add G.wT).add
    (.const 11)

/-! ### The answers -/

/-- `h = X^{(−t).val} · g^{α}` for the identity word `t` and the numeral `a` of `α`. -/
private def hS (w t a : List Bool) : List Bool :=
  mulGS G O w (powGS G O w (zX w) (negS G O w t)) (powGS G O w (zG w) a)

/-- The committed identity for `Init`: the recorded one, or the query. -/
private def tSel (w : List Bool) : List Bool := if sCom w then kT w else rX w
/-- The committed exponent for `Init`: the recorded one, or the drawn one. -/
private def aSel (w : List Bool) : List Bool := if sCom w then kA w else uS G O w

/-- `Init`'s answer `d ‖ g ‖ X ‖ Y ‖ h`. -/
private def ans0 (w : List Bool) : List Bool :=
  zD w ++ zG w ++ zX w ++ zY w ++ hS G O w (tSel w) (aSel G O w)

/-- Whether `KeyGen` answers a key: committed and `ID ≠ ID*`. -/
private def keyOk (w : List Bool) : Bool := sCom w && !decide (rX w = kT w)
/-- The residue of `ID − ID*`. -/
private def diffS (w : List Bool) : List Bool :=
  addS G O w (modS G O w (rX w)) (negS G O w (kT w))
/-- The residue of `1/(ID − ID*)`. -/
private def invD (w : List Bool) : List Bool := invS G O w (diffS G O w)
/-- `d_0 = Y^{(−α_1/(ID − ID*)).val} · (X^{ID.val} · h)^{r.val}`. -/
private def d0S (w : List Bool) : List Bool :=
  mulGS G O w (powGS G O w (zY w) (mulS G O w (negS G O w (kA w)) (invD G O w)))
    (powGS G O w (mulGS G O w (powGS G O w (zX w) (modS G O w (rX w)))
      (hS G O w (kT w) (kA w))) (uS G O w))
/-- `d_1 = Y^{(−1/(ID − ID*)).val} · g^{r.val}`. -/
private def d1S (w : List Bool) : List Bool :=
  mulGS G O w (powGS G O w (zY w) (negS G O w (invD G O w))) (powGS G O w (zG w) (uS G O w))
/-- `KeyGen`'s answer: `1 ‖ d_0 ‖ d_1`, or `⊥`. -/
private def ans1 (w : List Bool) : List Bool :=
  if keyOk w then true :: (d0S G O w ++ d1S G O w)
  else List.replicate ((aLen G ℓ 1).eval (rU w).length) false

/-- The first message `M_0` of a challenge query. -/
private def m0 (w : List Bool) : List Bool :=
  (rX w).take ((bb1Scheme G ℓ).msgLen.eval (rU w).length)
/-- The second message `M_1` of a challenge query. -/
private def m1 (w : List Bool) : List Bool :=
  (rX w).drop ((bb1Scheme G ℓ).msgLen.eval (rU w).length)
/-- The message `M_b`. -/
private def mB (w : List Bool) : List Bool := if b then m1 G ℓ w else m0 G ℓ w
/-- Whether both messages encode elements of `G_T` (`memT`). -/
private def valid (w : List Bool) : Bool :=
  (O.memT (pairEncode (zD w) (m0 G ℓ w))).headD false &&
    (O.memT (pairEncode (zD w) (m1 G ℓ w))).headD false
/-- The challenge `M_b · T ‖ Z ‖ Z^{α_1}`. -/
private def ctS (w : List Bool) : List Bool :=
  O.mulT (pairEncode (zD w) (pairEncode (mB G ℓ b w) (zT w))) ++ zZ w ++ powGS G O w (zZ w) (kA w)
/-- `Challenge`'s answer: `⊥` before `Init`, the recorded challenge, a fresh one, or `⊥`. -/
private def ans2 (w : List Bool) : List Bool :=
  if !sCom w then List.replicate ((aLen G ℓ 2).eval (rU w).length) false
  else if sChal w then sC G ℓ w
  else if valid G ℓ O w then ctS G ℓ O b w
  else List.replicate ((aLen G ℓ 2).eval (rU w).length) false

/-- The query is to `Init`. -/
private def isI (w : List Bool) : Bool := decide (rI w = [])
/-- The query is to `KeyGen`. -/
private def isK (w : List Bool) : Bool := decide (rI w = [true])

/-- The answer to the query. -/
private def ansW (w : List Bool) : List Bool :=
  if isI w then ans0 G O w else if isK w then ans1 G ℓ O w else ans2 G ℓ O b w
/-- The new commitment `o_1`. -/
private def newO1 (w : List Bool) : List Bool :=
  if isI w then pairEncode (tSel w) (aSel G O w) else sO1 w
/-- The new challenge record `o_2`. -/
private def newO2 (w : List Bool) : List Bool :=
  if isI w || isK w then sO2 G ℓ w
  else if sCom w && !sChal w && valid G ℓ O w then true :: ctS G ℓ O b w else sO2 G ℓ w

/-- **One round of the handler**: the answer and the new state
`⟨1^{j+1}, ⟨o_1', o_2'⟩⟩`, padded. -/
private def runF (w : List Bool) : List Bool :=
  pairEncode (ansW G ℓ O b w) (EnsembleLemmas.padL ((stLen G ℓ q).eval (rU w).length)
    (pairEncode (true :: sJ w) (pairEncode (newO1 G O w) (newO2 G ℓ O b w))))

/-! ### Polynomial time -/

section Poly

private theorem poly_hS (H : ArithmeticFP) {t a : List Bool → List Bool} (ht : PolyTimeComputable t)
    (ha : PolyTimeComputable a) : PolyTimeComputable fun w => hS G O w (t w) (a w) :=
  poly_mulGS G O (poly_powGS G O poly_zX (poly_negS G O H ht)) (poly_powGS G O poly_zG ha)
private theorem poly_tSel : PolyTimeComputable tSel :=
  polyTimeComputable_ite poly_sCom poly_kT poly_rX
private theorem poly_aSel (H : ArithmeticFP) : PolyTimeComputable (aSel G O) :=
  polyTimeComputable_ite poly_sCom poly_kA (poly_uS G O H)
private theorem poly_ans0 (H : ArithmeticFP) : PolyTimeComputable (ans0 G O) :=
  (((poly_zD.append poly_zG).append poly_zX).append poly_zY).append
    (poly_hS G O H poly_tSel (poly_aSel G O H))

private theorem poly_keyOk : PolyTimeComputable fun w => [keyOk w] :=
  polyTimeComputable_and poly_sCom (polyTimeComputable_not
    ((polyTimeComputable_pairEq.comp' (poly_rX.pairEncode poly_kT)).congr fun w => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]))
private theorem poly_diffS (H : ArithmeticFP) : PolyTimeComputable (diffS G O) :=
  poly_addS G O H (poly_modS G O H poly_rX) (poly_negS G O H poly_kT)
private theorem poly_invD (H : ArithmeticFP) : PolyTimeComputable (invD G O) :=
  poly_invS G O H (poly_diffS G O H)
private theorem poly_d0S (H : ArithmeticFP) : PolyTimeComputable (d0S G O) :=
  poly_mulGS G O (poly_powGS G O poly_zY
      (poly_mulS G O H (poly_negS G O H poly_kA) (poly_invD G O H)))
    (poly_powGS G O (poly_mulGS G O (poly_powGS G O poly_zX (poly_modS G O H poly_rX))
      (poly_hS G O H poly_kT poly_kA)) (poly_uS G O H))
private theorem poly_d1S (H : ArithmeticFP) : PolyTimeComputable (d1S G O) :=
  poly_mulGS G O (poly_powGS G O poly_zY (poly_negS G O H (poly_invD G O H)))
    (poly_powGS G O poly_zG (poly_uS G O H))
private theorem poly_ans1 (H : ArithmeticFP) : PolyTimeComputable (ans1 G ℓ O) :=
  polyTimeComputable_ite poly_keyOk
    (((polyTimeComputable_const [true]).append ((poly_d0S G O H).append (poly_d1S G O H))).congr
      fun _ => List.singleton_append)
    (EnsembleLemmas.polyTimeComputable_zeros (aLen G ℓ 1) poly_rU)

private theorem poly_m0 : PolyTimeComputable (m0 G ℓ) :=
  ((polyTimeComputable_pairTakePoly (bb1Scheme G ℓ).msgLen).comp'
    (poly_rU.pairEncode poly_rX)).congr fun w => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]; rfl
private theorem poly_m1 : PolyTimeComputable (m1 G ℓ) :=
  ((polyTimeComputable_pairDropPoly (bb1Scheme G ℓ).msgLen).comp'
    (poly_rU.pairEncode poly_rX)).congr fun w => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]; rfl
private theorem poly_mB : PolyTimeComputable (mB G ℓ b) :=
  polyTimeComputable_ite (polyTimeComputable_const [b]) (poly_m1 G ℓ) (poly_m0 G ℓ)
private theorem poly_valid : PolyTimeComputable fun w => [valid G ℓ O w] :=
  polyTimeComputable_and
    (polyTimeComputable_headD.comp' (O.memT_poly.comp' (poly_zD.pairEncode (poly_m0 G ℓ))))
    (polyTimeComputable_headD.comp' (O.memT_poly.comp' (poly_zD.pairEncode (poly_m1 G ℓ))))
private theorem poly_ctS : PolyTimeComputable (ctS G ℓ O b) :=
  ((O.mulT_poly.comp' (poly_zD.pairEncode ((poly_mB G ℓ b).pairEncode poly_zT))).append
    poly_zZ).append (poly_powGS G O poly_zZ poly_kA)
private theorem poly_ans2 : PolyTimeComputable (ans2 G ℓ O b) :=
  polyTimeComputable_ite (polyTimeComputable_not poly_sCom)
    (EnsembleLemmas.polyTimeComputable_zeros (aLen G ℓ 2) poly_rU)
    (polyTimeComputable_ite poly_sChal (poly_sC G ℓ)
      (polyTimeComputable_ite (poly_valid G ℓ O) (poly_ctS G ℓ O b)
        (EnsembleLemmas.polyTimeComputable_zeros (aLen G ℓ 2) poly_rU)))

private theorem poly_isI : PolyTimeComputable fun w => [isI w] :=
  polyTimeComputable_isNil.comp' poly_rI
private theorem poly_isK : PolyTimeComputable fun w => [isK w] :=
  (polyTimeComputable_pairEq.comp' (poly_rI.pairEncode (polyTimeComputable_const [true]))).congr
    fun w => by simp only [pairFstD_pairEncode, pairSndD_pairEncode]; rfl
private theorem poly_ansW (H : ArithmeticFP) : PolyTimeComputable (ansW G ℓ O b) :=
  polyTimeComputable_ite poly_isI (poly_ans0 G O H)
    (polyTimeComputable_ite poly_isK (poly_ans1 G ℓ O H) (poly_ans2 G ℓ O b))
private theorem poly_newO1 (H : ArithmeticFP) : PolyTimeComputable (newO1 G O) :=
  polyTimeComputable_ite poly_isI (poly_tSel.pairEncode (poly_aSel G O H)) poly_sO1
private theorem poly_newO2 : PolyTimeComputable (newO2 G ℓ O b) :=
  polyTimeComputable_ite (polyTimeComputable_or poly_isI poly_isK) (poly_sO2 G ℓ)
    (polyTimeComputable_ite (polyTimeComputable_and (polyTimeComputable_and poly_sCom
        (polyTimeComputable_not poly_sChal)) (poly_valid G ℓ O))
      (((polyTimeComputable_const [true]).append (poly_ctS G ℓ O b)).congr
        fun _ => List.singleton_append)
      (poly_sO2 G ℓ))

/-- **One round of the handler is polynomial-time**: every field is a pair projection, a fixed
word, an operation of `O`, an arithmetic function of `H`, the drawn exponent (`poly_uS`), a test,
a branch or a padding (`EnsembleLemmas.polyTimeComputable_padL`). -/
private theorem poly_runF (H : ArithmeticFP) : PolyTimeComputable (runF G ℓ O b q) :=
  (poly_ansW G ℓ O b H).pairEncode (EnsembleLemmas.polyTimeComputable_padL (stLen G ℓ q) poly_rU
    ((((polyTimeComputable_const [true]).append poly_sJ).congr
        fun _ => List.singleton_append).pairEncode
      ((poly_newO1 G O H).pairEncode (poly_newO2 G ℓ O b))))

end Poly

/-! ### The handler -/

/-- **The handler of the reduction `B`** [BB04, proof of Theorem 4.1] for the challenge bit `b`
and the budget `q`: state `⟨1^j, ⟨o_1, o_2⟩⟩` padded to `2q + 4ℓ + 4wG + wT + 11` bits, initially
`⟨[], ⟨[], []⟩⟩`; seed `q(κ)` blocks of `n · n` bits; the adversary's input is empty; one round
answers one query (`runF`); the output is the adversary's. -/
def handler (H : ArithmeticFP) : PolyHandler 3 (qLen G ℓ) (aLen G ℓ) where
  stateLen := stLen G ℓ q
  seedLen := q.mul ((blockLen G).mul (blockLen G))
  init _ := padFin _ (pairEncode [] (pairEncode [] []))
  run := runF G ℓ O b q
  poly := poly_runF G ℓ O b q H
  advIn _ := []
  advIn_poly := polyTimeComputable_const []
  out w := pairSndD (pairSndD w)
  out_poly := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD

variable (H : ArithmeticFP)

/-- The handler's seed has `q(κ) · (n · n)` bits: `(handler …).seedLen = q · (n · n)`. -/
theorem handler_seedLen : (handler G ℓ O b q H).seedLen = q.mul ((blockLen G).mul (blockLen G)) :=
  rfl

/-- The adversary runs on the empty input: `(handler …).advInput κ z ω = []`. -/
theorem handler_advInput (κ : ℕ) (z : List Bool)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) :
    (handler G ℓ O b q H).advInput κ z ω = [] := by
  rw [PolyHandler.advInput_eq]
  rfl

/-- The reduction outputs the adversary's output: `(handler …).result κ z ω s a = ⟦a⟧`. -/
theorem handler_result (κ : ℕ) (z : List Bool)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool)
    (s : Fin ((handler G ℓ O b q H).stateLen.eval κ) → Bool) {e : ℕ} (a : Fin e → Bool) :
    (handler G ℓ O b q H).result κ z ω s a = List.ofFn a := by
  rw [PolyHandler.result_eq]
  show pairSndD (pairSndD (pairEncode _ (pairEncode _ _))) = _
  rw [pairSndD_pairEncode, pairSndD_pairEncode]

/-- The seed length is `q(κ) · (n · n)`. -/
private theorem seedLen_eval (κ : ℕ) :
    (handler G ℓ O b q H).seedLen.eval κ =
      q.eval κ * ((blockLen G).eval κ * (blockLen G).eval κ) := by
  rw [handler_seedLen, PolyExpr.eval_mul, PolyExpr.eval_mul]

/-- **The seed as blocks**: `q(κ)` blocks of `n · n` bits, block `j` the `j`-th window of the
seed (`FunFamily.blocks`). -/
def seedBlocks (κ : ℕ) :
    (Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) ≃
      (Fin (q.eval κ) → Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool) :=
  (Equiv.arrowCongr (finCongr (seedLen_eval G ℓ O b q H κ)) (Equiv.refl Bool)).trans
    (FunFamily.blocks _ _)

/-- **Block `j` of the seed is its `j`-th window**:
`⟦seedBlocks … κ ω j⟧ = (⟦ω⟧.drop (j · n²)).take n²`. -/
theorem seedBlocks_window (κ : ℕ) (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool)
    (j : Fin (q.eval κ)) :
    List.ofFn (seedBlocks G ℓ O b q H κ ω j) =
      ((List.ofFn ω).drop (j * ((blockLen G).eval κ * (blockLen G).eval κ))).take
        ((blockLen G).eval κ * (blockLen G).eval κ) := by
  rw [seedBlocks, Equiv.trans_apply, FunFamily.ofFn_blocks, ofFn_arrowCongr_finCongr]

/-! ### The encoding of the simulator's states -/

/-- The commitment word: empty, or `⟨ID*, ⟦α_1⟧_{wG+1}⟩`. -/
private def o1Word (κ : ℕ) {d : List Bool} :
    Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order) →
      List Bool
  | none => []
  | some (t, α₁) => pairEncode (List.ofFn t) (natToList ((aWidth G).eval κ) α₁.val)

/-- The challenge record: empty, or `1 ‖ C`. -/
private def o2Word (κ : ℕ) : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) → List Bool
  | none => []
  | some c => true :: List.ofFn c

/-- The state word `⟨1^j, ⟨o_1, o_2⟩⟩` of the simulator's state `s` after `j` queries. -/
private def stWord (κ : ℕ) {d : List Bool} (s : BB1SimState G ℓ κ d) (j : ℕ) : List Bool :=
  pairEncode (List.replicate j true) (pairEncode (o1Word G ℓ κ s.1) (o2Word G ℓ κ s.2))

/-- The handler's encoding of the simulator's state `s` after `j` queries: `stWord`, padded. -/
private def stEnc (κ : ℕ) {d : List Bool} (s : BB1SimState G ℓ κ d) (j : ℕ) :
    Fin ((handler G ℓ O b q H).stateLen.eval κ) → Bool :=
  padFin _ (stWord G ℓ κ s j)



/-! ### Reading an encoded state -/

/-- The length of `stLen`: `2q + 4ℓ + 4wG + wT + 11`. -/
private theorem stLen_eval (κ : ℕ) :
    (stLen G ℓ q).eval κ = 2 * q.eval κ + 4 * ℓ.eval κ + 4 * G.wG.eval κ + G.wT.eval κ + 11 := by
  simp only [stLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  ring

/-- `|o_1| ≤ 2ℓ + 2 + (wG + 1)`. -/
private theorem length_o1Word_le (κ : ℕ) {d : List Bool}
    (o : Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order)) :
    (o1Word G ℓ κ o).length ≤ 2 * ℓ.eval κ + 2 + (G.wG.eval κ + 1) := by
  rcases o with _ | ⟨t, α₁⟩
  · simp only [o1Word, List.length_nil]
    omega
  · simp only [o1Word, length_pairEncode, List.length_ofFn, length_natToList, aWidth_eval]
    rw [bb1Scheme_idLen]

/-- `|o_2| ≤ 1 + (wT + 2 wG)`. -/
private theorem length_o2Word_le (κ : ℕ) (o : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    (o2Word G ℓ κ o).length ≤ 1 + (G.wT.eval κ + 2 * G.wG.eval κ) := by
  rcases o with _ | c
  · simp only [o2Word, List.length_nil]
    omega
  · simp only [o2Word, List.length_cons, List.length_ofFn]
    rw [bb1Scheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega

/-- The state word fits in the state: `|⟨1^j, ⟨o_1, o_2⟩⟩| ≤ stLen` for `j ≤ q`. -/
private theorem length_stWord_le (κ : ℕ) {d : List Bool} (s : BB1SimState G ℓ κ d) (j : ℕ)
    (hj : j ≤ q.eval κ) : (stWord G ℓ κ s j).length ≤ (stLen G ℓ q).eval κ := by
  have h1 := length_o1Word_le G ℓ κ s.1
  have h2 := length_o2Word_le G ℓ κ s.2
  rw [stWord, length_pairEncode, length_pairEncode, List.length_replicate, stLen_eval]
  omega

/-- **The fields of an encoded state**: for `j ≤ q`, the encoded state of `s` reads as the counter
`1^j`, the commitment word `o_1` and the challenge record `o_2` followed by `false`s. -/
private theorem fields_stEnc (κ : ℕ) {d : List Bool} (s : BB1SimState G ℓ κ d) (j : ℕ)
    (hj : j ≤ q.eval κ) :
    ∃ k, List.ofFn (stEnc G ℓ O b q H κ s j) =
      pairEncode (List.replicate j true)
        (pairEncode (o1Word G ℓ κ s.1) (o2Word G ℓ κ s.2 ++ List.replicate k false)) := by
  show ∃ k, List.ofFn (padFin ((stLen G ℓ q).eval κ) (stWord G ℓ κ s j)) = _
  rw [Collection.ofFn_padFin_of_le (length_stWord_le G ℓ q κ s j hj), stWord,
    ← GGMRed.pairEncode_append_right, ← GGMRed.pairEncode_append_right]
  exact ⟨_, rfl⟩

/-- The padding of a challenge record: its first bit is the record's (`false` when empty). -/
private theorem headD_o2Word (κ : ℕ) (o : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
    (k : ℕ) : (o2Word G ℓ κ o ++ List.replicate k false).headD false = o.isSome := by
  rcases o with _ | c
  · rcases k with _ | k <;> rfl
  · rfl

/-- The recorded challenge reads back from a padded record `1 ‖ C`. -/
private theorem take_o2Word (κ : ℕ) (c : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) (k : ℕ) :
    ((o2Word G ℓ κ (some c) ++ List.replicate k false).drop 1).take
      ((bb1Scheme G ℓ).ctLen.eval κ) = List.ofFn c := by
  simp only [o2Word, List.cons_append, List.drop_succ_cons, List.drop_zero]
  exact List.take_left' List.length_ofFn

section State

variable {κ : ℕ} {w : List Bool} {d : List Bool} {s : BB1SimState G ℓ κ d} {j : ℕ}

/-- The counter, the commitment and the padded record of a round input with an encoded state. -/
private theorem fields_rS (hj : j ≤ q.eval κ) (hS : rS w = List.ofFn (stEnc G ℓ O b q H κ s j)) :
    ∃ k, sJ w = List.replicate j true ∧ sO1 w = o1Word G ℓ κ s.1 ∧
      sR w = o2Word G ℓ κ s.2 ++ List.replicate k false := by
  obtain ⟨k, hk⟩ := fields_stEnc G ℓ O b q H κ s j hj
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [sJ_eq, hS, hk, pairFstD_pairEncode]
  · rw [sO1_eq, hS, hk, pairSndD_pairEncode, pairFstD_pairEncode]
  · rw [sR_eq, hS, hk, pairSndD_pairEncode, pairSndD_pairEncode]

end State



/-! ### One round on an encoded state -/

section Round

variable {κ : ℕ} {r : G.gen.Coins κ} {g X Y Z : (G.group κ (G.desc κ r)).G}
  {T : (G.group κ (G.desc κ r)).GT} {w : List Bool} {s : BB1SimState G ℓ κ (G.desc κ r)} {j : ℕ}


/-- **The encoded state after a round**: the new counter `1^{j+1}` and the new words `o_1`, `o_2`
of the state `s'`, padded, are the encoding of `s'` after `j + 1` queries. -/
private theorem padL_newState (hU : (rU w).length = κ) (hJ : sJ w = List.replicate j true)
    (s' : BB1SimState G ℓ κ (G.desc κ r)) {o1 o2 : List Bool} (h1 : o1 = o1Word G ℓ κ s'.1)
    (h2 : o2 = o2Word G ℓ κ s'.2) :
    EnsembleLemmas.padL ((stLen G ℓ q).eval (rU w).length)
        (pairEncode (true :: sJ w) (pairEncode o1 o2)) =
      List.ofFn (stEnc G ℓ O b q H κ s' (j + 1)) := by
  rw [hU, hJ, h1, h2, stEnc, EnsembleLemmas.ofFn_padFin_eq_padL, stWord, List.replicate_succ]
  rfl

/-- The commitment state of the round input: committed iff `s.1` is `some`. -/
private theorem sCom_of (hO1 : sO1 w = o1Word G ℓ κ s.1) : sCom w = s.1.isSome := by
  rw [sCom_eq, hO1]
  rcases s with ⟨_ | ⟨t, α₁⟩, c⟩
  · rfl
  · show (!decide (pairEncode _ _ = [])) = true
    rw [decide_eq_false (pairEncode_ne_nil _ _)]
    rfl

/-- The challenge record of the round input without its padding is `o_2`. -/
private theorem sO2_of (hU : (rU w).length = κ) {k : ℕ}
    (hR : sR w = o2Word G ℓ κ s.2 ++ List.replicate k false) :
    sO2 G ℓ w = o2Word G ℓ κ s.2 := by
  rw [sO2_eq, sChal_eq, hR, headD_o2Word]
  rcases s with ⟨o, _ | c⟩
  · rfl
  · show true :: sC G ℓ w = _
    rw [sC_eq, hR, hU, take_o2Word]
    rfl

/-- **The drawn exponent of the round**: the numeral `uS` is `⟦u.val⟧_{wG+1}` for the exponent
`u = draw (block j)` (`seedBlocks_window`, `uS_of_blkS`). -/
private theorem uS_of (hj : j < q.eval κ) (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool)
    (hU : (rU w).length = κ) (hD : zD w = G.desc κ r) (hW : rW w = List.ofFn ω)
    (hJ : sJ w = List.replicate j true) :
    uS G O w = natToList ((aWidth G).eval κ)
      (draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω ⟨j, hj⟩)).val := by
  refine uS_of_blkS G O hU hD _ ?_
  rw [blkS_eq, hW, hJ, hU, List.length_replicate, seedBlocks_window, nn_eval]

/-- `h = X^{(−t).val} · g^{α}` on encodings, for the identity word `⟦t⟧` and `α`'s numeral. -/
private theorem hS_ofFn (hZ : rZ w = tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (tw : List Bool) (α₁ : ZMod (G.group κ (G.desc κ r)).order) :
    hS G O w tw (natToList ((aWidth G).eval κ) α₁.val) =
      List.ofFn ((G.group κ (G.desc κ r)).encG
        (X ^ (-((listToNat tw : ℕ) : ZMod (G.group κ (G.desc κ r)).order)).val * g ^ α₁.val)) := by
  have hD := zD_of hZ
  rw [hS, zX_of hZ, zG_of hZ, powGS_ofFn G O hD, powGS_ofFn G O hD, mulGS_ofFn G O hD,
    listToNat_negS G O (listToNat_pS G O hD), listToNat_natToList_val]


/-- The length of the parameters' word `d ‖ g ‖ X ‖ Y ‖ h` is `ppLen`. -/
private theorem length_ppWord (h : (G.group κ (G.desc κ r)).G) :
    (G.desc κ r ++ List.ofFn ((G.group κ (G.desc κ r)).encG g) ++
      List.ofFn ((G.group κ (G.desc κ r)).encG X) ++ List.ofFn ((G.group κ (G.desc κ r)).encG Y) ++
      List.ofFn ((G.group κ (G.desc κ r)).encG h)).length = (aLen G ℓ 0).eval κ := by
  simp only [List.length_append, List.length_ofFn, G.length_desc]
  rw [aLen_zero, bb1Scheme_ppLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  ring

/-- **The `Init` round**: on the encoding of `s` after `j < q` queries, the handler answers and
updates the state as `drawStep` does with the exponent `u` drawn from block `j`.

**Proof sketch.** Read the round input's fields (`rU_input`, `rZ_input`, `fields_rS`), take the
`Init` branch of `runF`, and split on the commitment of `s` (`sCom_of`). Before a commitment the
committed pair is the query and the drawn exponent (`uS_of`); after one, the recorded pair
(`kT_eq`, `kA_eq`). In both cases `h = X^{(−t).val} · g^{α_1.val}` on encodings (`hS_ofFn`), the
answer `d ‖ g ‖ X ‖ Y ‖ h` has `ppLen` bits (`length_ppWord`), the identity reads as its
numeral's residue (`idToZ_padFin`, `BB1.idToZ_eq`), and the new state is the encoding of the
state of `drawStep_zero` after `j + 1` queries (`padL_newState`). -/
private theorem runF_zero (hj : j < q.eval κ)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) (x : Fin ((qLen G ℓ 0).eval κ) → Bool)
    (s : BB1SimState G ℓ κ (G.desc κ r)) (y : Fin ((aLen G ℓ 0).eval κ) → Bool)
    (s' : BB1SimState G ℓ κ (G.desc κ r))
    (h : drawStep G ℓ b κ (G.desc κ r) g X Y Z T 0 x s
      (draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω ⟨j, hj⟩)) = .pure (y, s')) :
    runF G ℓ O b q (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (0 : Fin 3) (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn (stEnc G ℓ O b q H κ s' (j + 1))) := by
  rw [drawStep_zero] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
  have hU : (rU (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
      (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (0 : Fin 3)
        (List.ofFn x))).length = κ := by
    rw [rU_input, List.length_replicate]
  have hZ := rZ_input (κ := κ) (z := tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (W := List.ofFn ω) (S := List.ofFn (stEnc G ℓ O b q H κ s j)) (i := 0) (X := List.ofFn x)
  have hD := zD_of hZ
  obtain ⟨k, hJ, hO1, hR⟩ := fields_rS G ℓ O b q H hj.le rS_input
  have hlen : (qLen G ℓ 0).eval κ = (bb1Scheme G ℓ).idLen.eval κ := by rw [qLen_zero]
  rw [runF, ansW, newO1, newO2, show isI _ = true by rw [isI, rI_input]; rfl, if_pos rfl,
    if_pos rfl, Bool.true_or, if_pos rfl, ans0, zD_of hZ, zG_of hZ, zX_of hZ, zY_of hZ,
    sO2_of G ℓ hU hR]
  rcases s with ⟨_ | ⟨t, α₁⟩, c⟩
  · -- before a commitment: the query and the drawn exponent
    have hcom : sCom (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ (none, c) j)) (0 : Fin 3)
          (List.ofFn x)) = false :=
      sCom_of G ℓ hO1
    rw [tSel, aSel, hcom, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, rX_input,
      uS_of G ℓ O b q H hj ω hU hD rW_input hJ, hS_ofFn G O hZ]
    simp only [Option.getD_none]
    congr 1
    · rw [ofFn_padFin_of_length (length_ppWord G ℓ _), idToZ_padFin G ℓ x hlen]
    · refine padL_newState G ℓ O b q H hU hJ _ ?_ rfl
      simp only [o1Word]
      rw [ofFn_padFin_of_length (by rw [List.length_ofFn, hlen])]
  · -- after a commitment: the recorded identity and exponent
    have hcom : sCom (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), c) j)) (0 : Fin 3)
        (List.ofFn x)) =
        true := sCom_of G ℓ hO1
    rw [tSel, aSel, hcom, if_pos rfl, if_pos rfl, kT_eq, kA_eq, hO1]
    simp only [o1Word, pairFstD_pairEncode, pairSndD_pairEncode, Option.getD_some]
    rw [hS_ofFn G O hZ]
    congr 1
    · rw [ofFn_padFin_of_length (length_ppWord G ℓ _), BB1.idToZ_eq,
        NumberTheory.bitsToNat_eq_listToNat]
    · exact padL_newState G ℓ O b q H hU hJ _ rfl rfl


/-- **The key of `KeyGen` on encodings, first component**: with the query `⟦x⟧`, the committed
identity `⟦t⟧`, `α_1`'s numeral and the drawn `u`'s numeral, `d0S` is the encoding of
`Y^{(−α_1/(x − t)).val} · (X^{x.val} · (X^{(−t).val} g^{α_1.val}))^{u.val}`, identities read as
their numerals' residues.

**Proof sketch.** Unfold `d0S` (this file) and rewrite each field and operation by its value on
encodings: the tuple's fields (`zX_of`, `zY_of`), the group operations (`powGS_ofFn`,
`mulGS_ofFn`, `hS_ofFn`) and the residue arithmetic (`listToNat_modS`, …, `listToNat_invS`),
then `ZMod.natCast_zmod_val`, `div_eq_mul_inv` and `sub_eq_add_neg` align the exponents. -/
private theorem d0S_of (hZ : rZ w = tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (xw tw : List Bool) (α₁ u : ZMod (G.group κ (G.desc κ r)).order) (hX : rX w = xw)
    (hT : kT w = tw) (hA : kA w = natToList ((aWidth G).eval κ) α₁.val)
    (hu : uS G O w = natToList ((aWidth G).eval κ) u.val) :
    d0S G O w = List.ofFn ((G.group κ (G.desc κ r)).encG
      (Y ^ (-α₁ / ((listToNat xw : ℕ) - (listToNat tw : ℕ) :
          ZMod (G.group κ (G.desc κ r)).order)).val *
        (X ^ ((listToNat xw : ℕ) : ZMod (G.group κ (G.desc κ r)).order).val *
          (X ^ (-((listToNat tw : ℕ) : ZMod (G.group κ (G.desc κ r)).order)).val * g ^ α₁.val)) ^
          u.val)) := by
  have hD := zD_of hZ
  have hp := listToNat_pS G O hD
  simp only [d0S, hT, hA, hu, hX, hS_ofFn G O hZ, zX_of hZ, zY_of hZ, powGS_ofFn G O hD,
    mulGS_ofFn G O hD, listToNat_natToList_val, listToNat_modS G O hp, listToNat_mulS G O hp,
    invD, listToNat_negS G O hp, listToNat_invS G O hp, diffS, listToNat_addS G O hp,
    ZMod.natCast_zmod_val, div_eq_mul_inv, sub_eq_add_neg]

/-- **The key of `KeyGen` on encodings, second component**: `d1S` is the encoding of
`Y^{(−1/(x − t)).val} · g^{u.val}`. -/
private theorem d1S_of (hZ : rZ w = tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (xw tw : List Bool) (u : ZMod (G.group κ (G.desc κ r)).order) (hX : rX w = xw)
    (hT : kT w = tw) (hu : uS G O w = natToList ((aWidth G).eval κ) u.val) :
    d1S G O w = List.ofFn ((G.group κ (G.desc κ r)).encG
      (Y ^ (-1 / ((listToNat xw : ℕ) - (listToNat tw : ℕ) :
          ZMod (G.group κ (G.desc κ r)).order)).val * g ^ u.val)) := by
  have hD := zD_of hZ
  have hp := listToNat_pS G O hD
  simp only [d1S, hu, hX, hT, zY_of hZ, zG_of hZ, powGS_ofFn G O hD, mulGS_ofFn G O hD,
    listToNat_natToList_val, listToNat_negS G O hp, invD, listToNat_invS G O hp, diffS,
    listToNat_addS G O hp, listToNat_modS G O hp, ZMod.natCast_zmod_val, neg_div, one_div,
    sub_eq_add_neg]

/-- **The `KeyGen` round**: on the encoding of `s` after `j < q` queries, the handler answers and
updates the state as `drawStep` does with the exponent `u` drawn from block `j`.

**Proof sketch.** Read the fields as for `Init` and take the `KeyGen` branch of `runF`, which
keeps `o_1` and `o_2`. Before `Init` the answer is `⊥` (`drawStep_one_none`). After it, split on
`⟦x⟧ = ⟦t⟧`: for the committed identity the answer is `⊥` (`drawStep_one_target`); otherwise it is
`1 ‖ d_0 ‖ d_1` with `r = u` drawn from block `j` (`drawStep_one_key`, `d0S_of`, `d1S_of`,
`uS_of`), of `1 + 2 wG` bits, with the identities read as their numerals' residues. The state is
re-encoded after `j + 1` queries (`padL_newState`). -/
private theorem runF_one (hj : j < q.eval κ)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) (x : Fin ((qLen G ℓ 1).eval κ) → Bool)
    (s : BB1SimState G ℓ κ (G.desc κ r)) (y : Fin ((aLen G ℓ 1).eval κ) → Bool)
    (s' : BB1SimState G ℓ κ (G.desc κ r))
    (h : drawStep G ℓ b κ (G.desc κ r) g X Y Z T 1 x s
      (draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω ⟨j, hj⟩)) = .pure (y, s')) :
    runF G ℓ O b q (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (1 : Fin 3) (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn (stEnc G ℓ O b q H κ s' (j + 1))) := by
  have hU : (rU (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
      (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (1 : Fin 3)
        (List.ofFn x))).length = κ := by
    rw [rU_input, List.length_replicate]
  have hZ := rZ_input (κ := κ) (z := tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (W := List.ofFn ω) (S := List.ofFn (stEnc G ℓ O b q H κ s j)) (i := 1) (X := List.ofFn x)
  have hD := zD_of hZ
  obtain ⟨k, hJ, hO1, hR⟩ := fields_rS G ℓ O b q H hj.le rS_input
  have hlen : (qLen G ℓ 1).eval κ = (bb1Scheme G ℓ).idLen.eval κ := by rw [qLen_one]
  have hlen1 : (aLen G ℓ 1).eval κ = 1 + 2 * G.wG.eval κ := by
    rw [aLen_one, PolyExpr.eval_add, PolyExpr.eval_const, bb1Scheme_skLen, PolyExpr.eval_mul,
      PolyExpr.eval_const]
    omega
  rw [runF, ansW, newO1, newO2, show isI _ = false by rw [isI, rI_input]; rfl,
    show isK _ = true by rw [isK, rI_input]; rfl, if_neg Bool.false_ne_true, if_pos rfl,
    if_neg Bool.false_ne_true, Bool.false_or, if_pos rfl, sO2_of G ℓ hU hR, ans1, keyOk]
  rcases s with ⟨_ | ⟨t, α₁⟩, c⟩
  · -- before `Init`: `⊥`
    rw [drawStep_one_none] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
    rw [sCom_of G ℓ hO1]
    simp only [Option.isSome_none, Bool.false_and, Bool.false_eq_true, if_false]
    congr 1
    · rw [hU, ofFn_zeroBits]
    · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl
  · have hcom := sCom_of G ℓ (s := (some (t, α₁), c)) hO1
    have hT : kT (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), c) j)) (1 : Fin 3)
          (List.ofFn x)) = List.ofFn t := by
      rw [kT_eq, hO1]
      simp only [o1Word, pairFstD_pairEncode]
    have hA : kA (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), c) j)) (1 : Fin 3)
          (List.ofFn x)) = natToList ((aWidth G).eval κ) α₁.val := by
      rw [kA_eq, hO1]
      simp only [o1Word, pairSndD_pairEncode]
    rw [hcom, rX_input, hT]
    simp only [Option.isSome_some, Bool.true_and]
    by_cases hx : List.ofFn x = List.ofFn t
    · -- the committed identity: `⊥`
      rw [drawStep_one_target G ℓ b κ _ g X Y Z T x t α₁ c _ hx] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
      rw [decide_eq_true hx, Bool.not_true, if_neg Bool.false_ne_true]
      congr 1
      · rw [hU, ofFn_zeroBits]
      · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl
    · -- another identity: the simulated key with `r = u`
      rw [drawStep_one_key G ℓ b κ _ g X Y Z T x t α₁ c _ hx] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
      rw [decide_eq_false hx, Bool.not_false, if_pos rfl,
        d0S_of G O hZ (List.ofFn x) (List.ofFn t) α₁ _ rX_input hT hA
          (uS_of G ℓ O b q H hj ω hU hD rW_input hJ),
        d1S_of G O hZ (List.ofFn x) (List.ofFn t) _ rX_input hT
          (uS_of G ℓ O b q H hj ω hU hD rW_input hJ)]
      congr 1
      · rw [ofFn_padFin_of_length (by
            simp only [List.length_cons, List.length_append, List.length_ofFn]
            rw [hlen1]; omega),
          idToZ_padFin G ℓ x hlen, BB1.idToZ_eq, NumberTheory.bitsToNat_eq_listToNat]
      · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl



/-- The ciphertext word `M · T ‖ Z ‖ Z^{α_1}` has `ctLen` bits. -/
private theorem length_ctWord (m : (G.group κ (G.desc κ r)).GT)
    (α₁ : ZMod (G.group κ (G.desc κ r)).order) :
    (List.ofFn ((G.group κ (G.desc κ r)).encT m) ++ List.ofFn ((G.group κ (G.desc κ r)).encG Z) ++
      List.ofFn ((G.group κ (G.desc κ r)).encG (Z ^ α₁.val))).length =
      (bb1Scheme G ℓ).ctLen.eval κ := by
  simp only [List.length_append, List.length_ofFn]
  rw [bb1Scheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  ring

/-- **The `Challenge` round**: on the encoding of `s` after `j < q` queries, the handler answers
and updates the state as `drawStep` does.

**Proof sketch.** Read the fields as for `Init` and take the `Challenge` branch of `runF`. Before
`Init` the answer is `⊥` (`drawStep_two_none`). After it, split on the recorded challenge
(`sChal_eq`, `headD_o2Word`): a recorded `C` is repeated (`drawStep_two_repeat`, `take_o2Word`).
Otherwise the handler's test `valid` is the test of `drawStep` that both halves of the query
(`take`/`drop` of `msgLen` bits) encode elements of `G_T` (`memT_headD`); if it holds, the selected
half is some `encT v`, and the answer `M_b · T ‖ Z ‖ Z^{α_1}` (`mulT_ofFn`, `powGS_ofFn`, of
`ctLen` bits by `length_ctWord`) is recorded as `o_2` (`drawStep_two_fresh`); if not, the answer is
`⊥` (`drawStep_two_invalid`). The state is re-encoded after `j + 1` queries
(`padL_newState`). -/
private theorem runF_two (hj : j < q.eval κ)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) (x : Fin ((qLen G ℓ 2).eval κ) → Bool)
    (s : BB1SimState G ℓ κ (G.desc κ r)) (y : Fin ((aLen G ℓ 2).eval κ) → Bool)
    (s' : BB1SimState G ℓ κ (G.desc κ r)) (u : ZMod (G.group κ (G.desc κ r)).order)
    (h : drawStep G ℓ b κ (G.desc κ r) g X Y Z T 2 x s u = .pure (y, s')) :
    runF G ℓ O b q (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (2 : Fin 3) (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn (stEnc G ℓ O b q H κ s' (j + 1))) := by
  classical
  have hU : (rU (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
      (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (2 : Fin 3)
        (List.ofFn x))).length = κ := by
    rw [rU_input, List.length_replicate]
  have hZ := rZ_input (κ := κ) (z := tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (W := List.ofFn ω) (S := List.ofFn (stEnc G ℓ O b q H κ s j)) (i := 2) (X := List.ofFn x)
  have hD := zD_of hZ
  obtain ⟨k, hJ, hO1, hR⟩ := fields_rS G ℓ O b q H hj.le rS_input
  have hmsg : (bb1Scheme G ℓ).msgLen.eval κ = G.wT.eval κ := by rw [bb1Scheme_msgLen]
  have hx2 : (List.ofFn x).length = (bb1Scheme G ℓ).msgLen.eval κ +
      (bb1Scheme G ℓ).msgLen.eval κ := by
    rw [List.length_ofFn, qLen_two, PolyExpr.eval_add]
  have hct : (aLen G ℓ 2).eval κ = (bb1Scheme G ℓ).ctLen.eval κ := by rw [aLen_two]
  rw [runF, ansW, newO1, newO2, show isI _ = false by rw [isI, rI_input]; rfl,
    show isK _ = false by rw [isK, rI_input]; rfl, if_neg Bool.false_ne_true,
    if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, Bool.false_or, if_neg Bool.false_ne_true,
    sO2_of G ℓ hU hR, ans2, sCom_of G ℓ hO1]
  rcases s with ⟨_ | ⟨t, α₁⟩, c⟩
  · -- before `Init`: `⊥`
    rw [drawStep_two_none] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
    simp only [Option.isSome_none, Bool.not_false, Bool.false_and, Bool.false_eq_true, if_false,
      if_true]
    congr 1
    · rw [hU, ofFn_zeroBits]
    · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl
  · have hchal : sChal (PolyHandler.input κ
        (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) (List.ofFn ω)
        (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), c) j)) (2 : Fin 3)
          (List.ofFn x)) = c.isSome := by
      rw [sChal_eq, hR, headD_o2Word]
    simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and,
      hchal]
    rcases c with _ | c
    · -- no challenge yet
      have hA : kA (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
          (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), none) j)) (2 : Fin 3)
            (List.ofFn x)) = natToList ((aWidth G).eval κ) α₁.val := by
        rw [kA_eq, hO1]
        simp only [o1Word, pairSndD_pairEncode]
      have hl0 : ((List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)).length = G.wT.eval κ := by
        rw [List.length_take, hx2, ← hmsg]
        omega
      have hl1 : ((List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ)).length = G.wT.eval κ := by
        rw [List.length_drop, hx2, ← hmsg]
        omega
      have hvalid : valid G ℓ O (PolyHandler.input κ
          (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) (List.ofFn ω)
          (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), none) j)) (2 : Fin 3) (List.ofFn x)) =
          decide ((∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
              (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
            (∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
              (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ))) := by
        rw [valid, m0, m1, rX_input, hU, memT_headD G O hD _ hl0, memT_headD G O hD _ hl1,
          Bool.decide_and]
      simp only [Option.isSome_none, Bool.not_false, Bool.true_and, Bool.false_eq_true,
        if_false]
      rw [hvalid]
      by_cases hc : (∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
            (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
          (∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
            (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ))
      · -- a fresh valid challenge: `M_b · T ‖ Z ‖ Z^{α_1}`, recorded
        rw [drawStep_two_fresh G ℓ b κ _ g X Y Z T x t α₁ u hc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
        rw [decide_eq_true hc, if_pos rfl, if_pos rfl]
        -- the selected message is an encoding `encT v`
        obtain ⟨v, hv⟩ : ∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
            (if b then (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ)
              else (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)) := by
          cases b
          · exact hc.1
          · exact hc.2
        have hmB : mB G ℓ b (PolyHandler.input κ
            (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) (List.ofFn ω)
            (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), none) j)) (2 : Fin 3) (List.ofFn x)) =
            List.ofFn ((G.group κ (G.desc κ r)).encT v) := by
          rw [hv, mB, m0, m1, rX_input, hU]
        have hct' : ctS G ℓ O b (PolyHandler.input κ
            (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) (List.ofFn ω)
            (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), none) j)) (2 : Fin 3) (List.ofFn x)) =
            List.ofFn ((G.group κ (G.desc κ r)).encT
              (BB1.decodeT (G.group κ (G.desc κ r)) (padFin _
                (if b then (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ)
                  else (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ))) * T)) ++
              List.ofFn ((G.group κ (G.desc κ r)).encG Z) ++
              List.ofFn ((G.group κ (G.desc κ r)).encG (Z ^ α₁.val)) := by
          rw [ctS, hmB, zT_of hZ, mulT_ofFn G O hD, zZ_of hZ, hA, powGS_ofFn G O hD,
            listToNat_natToList_val, ← hv, padFin_ofFn, BB1.decodeT_encT]
        rw [hct']
        congr 1
        · rw [ofFn_padFin_of_length (by rw [length_ctWord G ℓ, hct])]
        · refine padL_newState G ℓ O b q H hU hJ _ hO1 ?_
          simp only [o2Word]
          rw [ofFn_padFin_of_length (length_ctWord G ℓ _ _)]
      · -- a message outside `G_T`: `⊥`
        rw [drawStep_two_invalid G ℓ b κ _ g X Y Z T x t α₁ u hc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
        rw [decide_eq_false hc]
        simp only [Bool.false_eq_true, if_false]
        congr 1
        · rw [hU, ofFn_zeroBits]
        · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl
    · -- a recorded challenge: repeated
      rw [drawStep_two_repeat] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
      simp only [Option.isSome_some, Bool.not_true, Bool.false_and, if_true, Bool.false_eq_true,
        if_false]
      congr 1
      · rw [sC_eq, hR, hU, take_o2Word,
          ofFn_padFin_of_length (by rw [List.length_ofFn, hct])]
      · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl


end Round


/-! ### The handler's run -/

/-- **One query to the handler on an encoded state is one query to `drawStep`**: from the
encoding of `s` after `j < q` queries, the handler answers like `drawStep` with the exponent of
the tape `V j = draw (block j)`, and moves to the encoding of the new state after `j + 1`
queries.

**Proof sketch.** The tape's `j`-th entry is the draw from block `j` (`AdaptiveCPA.extTape_of_lt`),
and `drawStep` answers with some `(y, s')` (`exists_drawStep_eq_pure`), which is the tape run's
step (`ETTGame.tapeImpl_apply`). The handler's call answers with the first component of `runF` on
the round input (`PolyHandler.impl_apply`, `PolyHandler.answer_of_run_eq`), which the round
lemmas `runF_zero`, `runF_one`, `runF_two` identify with `y` and the encoding of `s'`. -/
private theorem handler_impl_stEnc (κ : ℕ) (r : G.gen.Coins κ)
    (g X Y Z : (G.group κ (G.desc κ r)).G) (T : (G.group κ (G.desc κ r)).GT)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) (i : Fin 3)
    (x : Fin ((qLen G ℓ i).eval κ) → Bool)
    (st : BB1SimState G ℓ κ (G.desc κ r) × ℕ) (hj : st.2 < q.eval κ) :
    ∃ (y : Fin ((aLen G ℓ i).eval κ) → Bool) (st' : BB1SimState G ℓ κ (G.desc κ r) × ℕ),
      ETTGame.tapeImpl (spec := bitSpecAt (qLen G ℓ) (aLen G ℓ) κ)
          (drawStep G ℓ b κ (G.desc κ r) g X Y Z T)
          (AdaptiveCPA.extTape fun j => draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω j))
          i x st = .pure (y, st') ∧ st'.2 ≤ st.2 + 1 ∧
        (handler G ℓ O b q H).impl κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) ω i
          x (stEnc G ℓ O b q H κ st.1 st.2) = .pure (y, stEnc G ℓ O b q H κ st'.1 st'.2) := by
  obtain ⟨s, j⟩ := st
  have hV : AdaptiveCPA.extTape (fun j => draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω j)) j =
      draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω ⟨j, hj⟩) :=
    AdaptiveCPA.extTape_of_lt _ hj
  obtain ⟨y, s', hds⟩ := exists_drawStep_eq_pure G ℓ b κ (G.desc κ r) g X Y Z T i x s
    (draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω ⟨j, hj⟩))
  refine ⟨y, (s', j + 1), ?_, le_rfl, ?_⟩
  · rw [ETTGame.tapeImpl_apply, hV, hds, OracleComp.pure_bind]
  · rw [PolyHandler.impl_apply]
    refine congrArg OracleComp.pure (PolyHandler.answer_of_run_eq _ ?_)
    show runF G ℓ O b q _ = _
    match i, x, y, hds with
    | 0, x, y, hds => exact runF_zero G ℓ O b q H hj ω x s y s' hds
    | 1, x, y, hds => exact runF_one G ℓ O b q H hj ω x s y s' hds
    | 2, x, y, hds => exact runF_two G ℓ O b q H hj ω x s y s' _ hds

/-- **The handler's run is the run of `drawStep` with exponents from the seed** [BB04, proof of
Theorem 4.1, the algorithm `B`]: for a computation `c` with at most `q(κ)` queries, simulating
`c` against the handler on the Decision BDH string of `(g, X, Y, Z, T)` and the seed `ω`, from its
initial state, is simulating `c` against `drawStep` with the exponent of the `j`-th query read
from the tape `V j = draw (block j of ω)` (`ETTGame.tapeImpl`), from the empty state, with the
final state read through an encoding `f`.

**Proof sketch.** `Games.simulate_eq_of_abs_bounded` with the counter of queries and the encoding
of the simulator's states: from the encoding of a state after `j < q(κ)` queries, the handler and
`drawStep` give the same answer and corresponding states (`handler_impl_stEnc`: the round
function `runF` reads the counter, the commitment and the challenge record from the padded state,
draws the exponent from block `j` of the seed, and computes the answer of `Init`, `KeyGen` or
`Challenge` with the operations of `O` and the arithmetic of `H`, `runF_zero`, `runF_one`,
`runF_two`); the initial state is the encoding of the empty state. -/
theorem simulate_handler (κ : ℕ) (r : G.gen.Coins κ) (g X Y Z : (G.group κ (G.desc κ r)).G)
    (T : (G.group κ (G.desc κ r)).GT) (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool)
    {α : Type} (c : OracleComp (bitSpecAt (qLen G ℓ) (aLen G ℓ) κ) α)
    (hc : c.CostBoundedBy (fun _ => 1) (q.eval κ)) :
    ∃ f : BB1SimState G ℓ κ (G.desc κ r) × ℕ → (Fin ((handler G ℓ O b q H).stateLen.eval κ) → Bool),
      simulate ((handler G ℓ O b q H).impl κ
          (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) ω) c
          ((handler G ℓ O b q H).init κ) =
        (simulate (ETTGame.tapeImpl (spec := bitSpecAt (qLen G ℓ) (aLen G ℓ) κ)
          (drawStep G ℓ b κ (G.desc κ r) g X Y Z T)
          (AdaptiveCPA.extTape fun j => draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω j)))
          c ((none, none), 0)).bind fun p => .pure (p.1, f p.2) := by
  refine ⟨fun st => stEnc G ℓ O b q H κ st.1 st.2, ?_⟩
  have hinit : (handler G ℓ O b q H).init κ =
      stEnc G ℓ O b q H κ (d := G.desc κ r) (none, none) 0 := rfl
  rw [hinit]
  exact simulate_eq_of_abs_bounded _ _ (fun st => stEnc G ℓ O b q H κ st.1 st.2) Prod.snd
    (q.eval κ) (fun i x st hst => handler_impl_stEnc G ℓ O b q H κ r g X Y Z T ω i x st hst) c
    (q.eval κ) hc ((none, none), 0) (by omega)


end

end BB1Machine

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased

## ===== TCSlib/Cryptography/Candidates/DiscreteLog.lean (Lean, at 4f4a7592a54cf82fa04f96b83645d7936672614c) =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.NonUniform
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Candidates.Concrete
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.NumberTheory.Units
import Mathlib.Data.Nat.Size
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The discrete-logarithm assumption and the discrete-logarithm collection

The discrete-logarithm material of [PS10, §2.8]: the *discrete-log assumption* for a family
of prime-order groups [PS10, Assumption 52.2] and the collection
`DL = {f_{q,g}(x) = g^x : Z_q → G_q}` with indices `(q, g)`, which is a collection of
one-way functions under that assumption [PS10, Theorem 52.3].

**The groups.** Following the text's own instantiation (p. 52, "one usually picks a prime of
the form `p = 2q + 1` … and then sets `G` to be the subgroup of squares in `Z_p^*`"), the
prime-order group `G_q` is the subgroup of squares of `Z_p^* = (ZMod p)ˣ` for a *safe prime*
`p = 2q + 1`. A group instance is the string index `⟨p, ⟨m, g⟩⟩` of three `n`-bit numerals:
the prime `p`, the order `m` of the group generated by `g` (the domain of the exponentiation
is `Z_m`), and the generator `g` (`ExpValid`: `orderOf g = m` in `Z_p`). The same index
format serves the full-group collection of `TCSlib.Cryptography.Candidates.DiscreteLogHardcore`
(`m = p − 1`, `g` a generator of `Z_p^*`, [PS10, Lemma 84.1]) and the El Gamal keys of
`TCSlib.Cryptography.Encryption.PublicKey.ElGamal`, so the exponentiation collection is built once,
generically over a validity predicate `V` on indices: `expCollection`.

**The sampler of instances.** The text samples `q ← Π_n; g ← Gen_{G_q}` and notes (p. 52–53)
that no efficient procedure for safe primes is known. Foundation decision D10 and the
deviation register (#15) replace the ideal sampler by an explicit *instance generator*
`ExpGroupGen V`: a PPT `Gen(1^n)` whose outputs, from a threshold `n₀` on, are valid indices
of three `n`-bit numerals. The assumption and the theorems are relative to the generator;
every statement about machines is conditional on the arithmetic bundle `ArithmeticFP` (D11).
Below the threshold the collection's own generator `expGen` outputs the fixed valid instance
`dlDefaultIndex = ⟨3, ⟨2, 2⟩⟩`, so that every generated index is valid and the sampler's
outputs decode at every parameter (`Collection.sample_spec`, run-3 audit P3-1); the
collection `expCollection H G hV` therefore takes the validity bridge `hV : ∀ i, V i → ExpValid i`
as an argument.

**Full-length primes.** Where a proof divides by `q` or `p − 1` (Lemma 84.1's range reduction,
the `1/q` term of Theorem 107.3) the proofs use full length `2^{n−1} ≤ p` (a convenience: the
hypothesis is dispensable in both headline theorems, gate 03f1 review, M1). This is
demanded only *except on a negligible set of coins* (`ExpGroupGen.FullLengthExcept δ` with
`Negligible δ`): a strict-PPT generator may fall back to a fixed instance when its rejection
loop fails (D10), and demanding full length on every coin string (`ExpGroupGen.FullLength`)
would require a deterministic polynomial-time construction of full-length primes of the
required form, which is not known (run-3 audit P8-2). The rejection sampler of numbers below
`m` (`sampleBelowL`) is within `(1/2)^n` of uniform (`statClose_sampleBelowL`, D10), the
closeness fact shared by the collection's domain sampler and the El Gamal samplers.

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Concretely: the adversary of Assumption 52.2 receives `⟨1^n, ⟨i, g^x⟩⟩`
with the whole index `i = ⟨p, ⟨q, g⟩⟩` (the text passes `g^x` only, source error 8), the
exponent `x ← Z_q` is ideal uniform in the experiment while the honest domain sampler is a
truncated rejection sampler within `2^{-n}` of uniform (D10), the answer is read as an
`n`-bit numeral (wrong length = failure, D5), "`Pr[…] < ε(n)` for a negligible `ε`" is
"`Pr[…]` is negligible", and the ideal "`q ← Π_n; g ← Gen_{G_q}`" is the law of the instance
generator. Theorem 52.3's `R_i = G_p`, `f_{p,g}` are read as `G_q`, `f_{q,g}` (source
error 8) and `k` as `n`.

## Main definitions

* `TCSlib.Cryptography.Candidates.dlP`, `dlM`, `dlG`, `dlW`, `WellFormedIndex` — reading the
  index `⟨p, ⟨m, g⟩⟩`; `TCSlib.Cryptography.Candidates.ExpValid` — valid indices.
* `TCSlib.Cryptography.Candidates.expOrd`, `expEnc`, `expDec`, `expF`, `expEval` — the
  domain `Z_m`, its encoding, the function `x ↦ g^x mod p` and its evaluator.
* `TCSlib.Cryptography.Candidates.ExpGroupGen` — instance generators;
  `ExpGroupGen.dlProb`, `ExpGroupGen.DLHard` — the discrete-log experiment and hardness;
  `ExpGroupGen.FullLength`, `ExpGroupGen.FullLengthExcept` — full-length primes (on every
  coin string / except on a set of coins of probability `δ n`).
* `TCSlib.Cryptography.Candidates.sampleBelowL`, `expSampler`, `dlDefaultIndex`, `expGen`,
  `expCollection` — the exponentiation collection of an instance generator.
* `TCSlib.Cryptography.Candidates.SafePrimeValid`, `SafePrimeGen`,
  `TCSlib.Cryptography.Candidates.DLAssumption` — [PS10, Assumption 52.2];
  `TCSlib.Cryptography.Candidates.dlCollection` — the collection `DL` [PS10, Theorem 52.3].

## Main results

* `TCSlib.Cryptography.Candidates.expF_injective` — `x ↦ g^x` is injective on `Z_m` at a
  valid index (the remark after [PS10, Theorem 52.3]; Claim-53.2 of the inventory, proved).
* `TCSlib.Cryptography.Candidates.expEval_spec`, `expDec_expEnc` — the collection data
  (proved).
* `TCSlib.Cryptography.Candidates.statClose_sampleBelowL` — the rejection sampler of numbers
  below `m` is within `(1/2)^n` of uniform (D10);
  `ExpGroupGen.FullLength.fullLengthExcept`, `ExpGroupGen.FullLength.exists_fullLengthExcept` —
  full length on every coin string is the `δ = 0` case (proved).
* `TCSlib.Cryptography.Candidates.expCollection_invProbAt_le` — inverting the collection is
  the discrete-log experiment; `expCollection_sampleClose`, `expCollection_oneWay`.
* `TCSlib.Cryptography.Candidates.dlCollection_oneWay` — [PS10, Theorem 52.3].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.8: Definition 52.1, Assumption 52.2, Theorem 52.3 and the remarks on pp. 52–53.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (the concrete inversion experiment).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## Group instances `⟨p, ⟨m, g⟩⟩` -/

/-- The prime `p` read from the index `⟨p, ⟨m, g⟩⟩`. -/
def dlP (i : List Bool) : ℕ := listToNat (pairFstD i)

/-- The defining equation of `dlP`: `dlP i = listToNat (pairFstD i)`, the number read from the
first component of `⟨p, ⟨m, g⟩⟩`. -/
theorem dlP_eq (i : List Bool) : dlP i = listToNat (pairFstD i) := rfl

/-- The group order `m` read from the index `⟨p, ⟨m, g⟩⟩` (the domain of the exponentiation
is `Z_m`; `m = q` for the prime-order groups, `m = p − 1` for `Z_p^*`). -/
def dlM (i : List Bool) : ℕ := listToNat (pairFstD (pairSndD i))

/-- The defining equation of `dlM`: `dlM i = listToNat (pairFstD (pairSndD i))`, the number read
from the middle component of `⟨p, ⟨m, g⟩⟩`. -/
theorem dlM_eq (i : List Bool) : dlM i = listToNat (pairFstD (pairSndD i)) := rfl

/-- The generator `g` read from the index `⟨p, ⟨m, g⟩⟩`. -/
def dlG (i : List Bool) : ℕ := listToNat (pairSndD (pairSndD i))

/-- The defining equation of `dlG`: `dlG i = listToNat (pairSndD (pairSndD i))`, the number read
from the last component of `⟨p, ⟨m, g⟩⟩`. -/
theorem dlG_eq (i : List Bool) : dlG i = listToNat (pairSndD (pairSndD i)) := rfl

/-- The numeral width of an index: the width of the numeral of `p` (all group elements are
encoded with this width). -/
def dlW (i : List Bool) : ℕ := (pairFstD i).length

/-- An index is *well formed at parameter `n`* when it is a pair `⟨a, ⟨b, c⟩⟩` of three
`n`-bit numerals (the text's "`p` of length `n`"). -/
def WellFormedIndex (n : ℕ) (i : List Bool) : Prop :=
  ∃ a b c : List Bool, i = pairEncode a (pairEncode b c) ∧ a.length = n ∧ b.length = n ∧ c.length = n

/-- Unfolding `WellFormedIndex`: `i` is well formed at `n` iff `i = ⟨a, ⟨b, c⟩⟩` for three
`n`-bit strings `a`, `b`, `c`. -/
theorem wellFormedIndex_iff (n : ℕ) (i : List Bool) :
    WellFormedIndex n i ↔ ∃ a b c : List Bool,
      i = pairEncode a (pairEncode b c) ∧ a.length = n ∧ b.length = n ∧ c.length = n :=
  Iff.rfl

/-- The width of a well-formed index is `n`. -/
theorem WellFormedIndex.dlW_eq {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) : dlW i = n := by
  obtain ⟨a, b, c, rfl, ha, -, -⟩ := h
  simp [dlW, ha]

/-- A well-formed index at parameter `n` has length `5n + 4`. -/
theorem WellFormedIndex.length_eq {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) :
    i.length = 5 * n + 4 := by
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := h
  simp only [length_pairEncode, ha, hb, hc]
  ring

/-- `p < 2^{dlW i}`: the prime fits its numeral. -/
theorem dlP_lt_two_pow (i : List Bool) : dlP i < 2 ^ dlW i := listToNat_lt_two_pow _

/-- An index `⟨p, ⟨m, g⟩⟩` is *valid* when `p` is prime, `0 < m < p`, `0 < g < p`, and `g` has
order exactly `m` in `Z_p` (so `x ↦ g^x` is a bijection of `Z_m` onto the subgroup generated
by `g`, [PS10, Definition 52.1]). (Not efficiently decidable from the index — generators only
ever output valid indices.) -/
def ExpValid (i : List Bool) : Prop :=
  (dlP i).Prime ∧ 0 < dlM i ∧ dlM i < dlP i ∧ 0 < dlG i ∧ dlG i < dlP i ∧
    orderOf ((dlG i : ℕ) : ZMod (dlP i)) = dlM i

/-- Unfolding `ExpValid`: `i` is valid iff `p` is prime, `0 < m < p`, `0 < g < p` and `g` has
order `m` in `Z_p` (with `p = dlP i`, `m = dlM i`, `g = dlG i`). -/
theorem expValid_iff (i : List Bool) :
    ExpValid i ↔ (dlP i).Prime ∧ 0 < dlM i ∧ dlM i < dlP i ∧ 0 < dlG i ∧ dlG i < dlP i ∧
      orderOf ((dlG i : ℕ) : ZMod (dlP i)) = dlM i :=
  Iff.rfl

noncomputable instance : DecidablePred ExpValid := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The order of the domain at an index: `m` for a valid index and `1` otherwise (so that the
domain `Z_m` is always a finite group). -/
noncomputable def expOrd (i : List Bool) : ℕ := if ExpValid i then dlM i else 1

instance (i : List Bool) : NeZero (expOrd i) := by
  unfold expOrd
  split_ifs with h
  · exact ⟨h.2.1.ne'⟩
  · exact ⟨one_ne_zero⟩

/-- `expOrd` of a valid index is `m`. -/
theorem expOrd_of_valid {i : List Bool} (h : ExpValid i) : expOrd i = dlM i := if_pos h

/-- `expOrd` of an invalid index is `1`. -/
theorem expOrd_of_not_valid {i : List Bool} (h : ¬ ExpValid i) : expOrd i = 1 := if_neg h

/-- The order of the domain fits the numeral width: `expOrd i ≤ 2^{dlW i}`. -/
theorem expOrd_le_two_pow (i : List Bool) : expOrd i ≤ 2 ^ dlW i := by
  unfold expOrd
  split_ifs with h
  · exact (h.2.2.1.trans (dlP_lt_two_pow i)).le
  · exact Nat.one_le_two_pow

/-- The residue of an element of the domain fits the numeral width. -/
theorem val_lt_two_pow_dlW (i : List Bool) (x : ZMod (expOrd i)) : x.val < 2 ^ dlW i :=
  lt_of_lt_of_le (ZMod.val_lt x) (expOrd_le_two_pow i)

/-- `g` is coprime to `p` at a valid index (`0 < g < p` and `p` prime). -/
theorem coprime_dlG_dlP {i : List Bool} (h : ExpValid i) : Nat.Coprime (dlG i) (dlP i) :=
  ((Nat.Prime.coprime_iff_not_dvd h.1).2 (Nat.not_dvd_of_pos_of_lt h.2.2.2.1 h.2.2.2.2.1)).symm

/-- The generator `g` as a unit of `Z_p` at a valid index. -/
noncomputable def expUnit {i : List Bool} (h : ExpValid i) : (ZMod (dlP i))ˣ :=
  ZMod.unitOfCoprime (dlG i) (coprime_dlG_dlP h)

/-- The value of `expUnit` is `g mod p`. -/
theorem coe_expUnit {i : List Bool} (h : ExpValid i) :
    (expUnit h : ZMod (dlP i)) = ((dlG i : ℕ) : ZMod (dlP i)) := ZMod.coe_unitOfCoprime _ _

/-- The order of the unit `g` is `m` [PS10, Definition 52.1, "`g` is a generator"]. -/
theorem orderOf_expUnit {i : List Bool} (h : ExpValid i) : orderOf (expUnit h) = dlM i := by
  rw [← orderOf_units, coe_expUnit]
  exact h.2.2.2.2.2

/-! ## The domain `Z_m`, its encoding and the function `x ↦ g^x` -/

/-- The string encoding of `x ∈ Z_m`: its residue as a numeral of the index width. -/
noncomputable def expEnc (i : List Bool) (x : ZMod (expOrd i)) : List Bool := natToList (dlW i) x.val

/-- The defining equation of `expEnc`: `expEnc i x = ⟦x.val⟧_{dlW i}`, the residue of `x` as a
numeral of the index width. -/
theorem expEnc_eq (i : List Bool) (x : ZMod (expOrd i)) : expEnc i x = natToList (dlW i) x.val :=
  rfl

/-- The decoder of `Z_m`: a numeral of the index width reading as a number below `m`. -/
noncomputable def expDec (i : List Bool) (w : List Bool) : Option (ZMod (expOrd i)) :=
  if w.length = dlW i ∧ listToNat w < expOrd i then some ((listToNat w : ℕ) : ZMod (expOrd i))
  else none

/-- Decoding inverts encoding (the clause `decD_encD` of `Collection`). -/
theorem expDec_expEnc (i : List Bool) (x : ZMod (expOrd i)) : expDec i (expEnc i x) = some x := by
  have hl : listToNat (expEnc i x) = x.val := listToNat_natToList (val_lt_two_pow_dlW i x)
  rw [expDec, if_pos ⟨by simp [expEnc], by rw [hl]; exact ZMod.val_lt x⟩, hl,
    ZMod.natCast_zmod_val]

/-- **Decoding is canonical** (the clause `Collection.encD_decD` of `expCollection`; gate 03b,
finding 1): a string that `expDec i` decodes to `x` is `expEnc i x`, since it is a numeral of
the index width reading below `m` (`natToList_val_natCast`). -/
theorem expEnc_of_expDec {i w : List Bool} {x : ZMod (expOrd i)} (h : expDec i w = some x) :
    expEnc i x = w := by
  rw [expDec] at h
  split_ifs at h with hw
  rw [← Option.some.inj h, expEnc, natToList_val_natCast hw.1 hw.2]

/-- **The function `f_{q,g}(x) = g^x mod p`** [PS10, Theorem 52.3] as a string function on
`Z_m`: the numeral of `g^x mod p` of the index width (the evaluator `modExpStr` mirrored). -/
noncomputable def expF (i : List Bool) (x : ZMod (expOrd i)) : List Bool :=
  natToList (dlW i) (dlG i ^ x.val % dlP i)

/-- The defining equation of `expF`: `expF i x = ⟦g^x mod p⟧_{dlW i}`, the numeral of
`dlG i ^ x.val % dlP i` of the index width. -/
theorem expF_eq (i : List Bool) (x : ZMod (expOrd i)) :
    expF i x = natToList (dlW i) (dlG i ^ x.val % dlP i) := rfl

/-- The evaluator of the exponentiation collection on `⟨⟨p, ⟨m, g⟩⟩, x⟩`: one modular
exponentiation `modExpStr ⟨g, ⟨x, p⟩⟩` [PS10, Theorem 52.3, "it is easy to evaluate"]. -/
def expEval (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD (pairSndD (pairFstD z)))
    (pairEncode (pairSndD z) (pairFstD (pairFstD z))))

/-- The evaluator computes `expF` on encoded elements. -/
theorem expEval_spec (i : List Bool) (x : ZMod (expOrd i)) :
    expEval (pairEncode i (expEnc i x)) = expF i x := by
  have hl : listToNat (natToList (dlW i) x.val) = x.val :=
    listToNat_natToList (val_lt_two_pow_dlW i x)
  simp only [expEval, expF, expEnc, dlG, dlP, dlW, pairFstD_pairEncode, pairSndD_pairEncode,
    modExpStr_pairEncode] at hl ⊢
  rw [hl]

/-- The evaluator is polynomial-time given modular exponentiation. -/
theorem polyTimeComputable_expEval (H : ArithmeticFP) : PolyTimeComputable expEval :=
  H.modExp.comp ((polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    polyTimeComputable_pairFstD)).pairEncode (polyTimeComputable_pairSndD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)))

/-- **`x ↦ g^x` is injective on `Z_m`** at a valid index (the remark after
[PS10, Theorem 52.3]: "each function is a permutation"; Claim-53.2 of the inventory): since
`g` has order `m` in `Z_p`, `g^a = g^b` forces `a ≡ b (mod m)`.

**Proof sketch.** Both numerals have width `dlW i` and read as numbers below `p < 2^{dlW i}`
(`natToList_injOn`), so `g^a ≡ g^b (mod p)`; in the group of units, `pow_eq_pow_iff_modEq`
with `orderOf_expUnit` gives `a ≡ b (mod m)`, and `a, b < m`. -/
theorem expF_injective {i : List Bool} (h : ExpValid i) : Function.Injective (expF i) := by
  intro x y hxy
  have hlt : ∀ e : ℕ, dlG i ^ e % dlP i < 2 ^ dlW i :=
    fun e => (Nat.mod_lt _ h.1.pos).trans (dlP_lt_two_pow i)
  have h1 : dlG i ^ x.val % dlP i = dlG i ^ y.val % dlP i := natToList_injOn (hlt _) (hlt _) hxy
  have h2 : expUnit h ^ x.val = expUnit h ^ y.val := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, coe_expUnit, ← Nat.cast_pow,
      ← Nat.cast_pow, ← ZMod.natCast_mod, h1, ZMod.natCast_mod]
  have h3 := pow_eq_pow_iff_modEq.1 h2
  rw [orderOf_expUnit h] at h3
  have hx : x.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt x) (expOrd_of_valid h)
  have hy : y.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt y) (expOrd_of_valid h)
  exact ZMod.val_injective _ (h3.eq_of_lt_of_lt hx hy)

/-! ## Instance generators and the discrete-log experiment -/

/-- An **instance generator** for exponentiation collections with validity predicate `V`:
a PPT `Gen(1^n)` whose outputs, from the threshold `n₀` on, satisfy `V` and are well-formed
indices of three `n`-bit numerals. The formal counterpart of the text's
"`q ← Π_n; g ← Gen_{G_q}`" [PS10, Assumption 52.2] and "pick a safe prime `p = 2q + 1` of
length `n`" [PS10, Algorithm 106.2]; the text itself notes (pp. 52–53) that no efficient
sampler of safe primes with generators is known, so the generator is a hypothesis object.

**Deviation:** the ideal samplers of the text are replaced by a PPT generator relative to
which the assumptions are stated (D10, deviations register #15); outputs below `n₀` are
unconstrained (the degenerate parameters). -/
structure ExpGroupGen (V : List Bool → Prop) where
  /-- The generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- The threshold from which the outputs are valid. -/
  n₀ : ℕ
  /-- Outputs are valid from the threshold on. -/
  valid : ∀ n (r : gen.Coins n), n₀ ≤ n → V (gen.runAt n [] r)
  /-- Outputs are well-formed indices of `n`-bit numerals from the threshold on. -/
  wellFormed : ∀ n (r : gen.Coins n), n₀ ≤ n → WellFormedIndex n (gen.runAt n [] r)

namespace ExpGroupGen

variable {V : List Bool → Prop} (G : ExpGroupGen V)

/-- The generator outputs primes of *full length* `n` on **every** coin string: `2^{n-1} ≤ p`
at every generated index from `n₀` on (the text's "`p` of length `n`" read with a leading
`1`; `p < 2^n` already follows from `wellFormed`). Too strong as a hypothesis of a theorem
(see `FullLengthExcept`, run-3 audit P8-2): together with `valid` it asks for a deterministic
polynomial-time construction (run the generator on the all-zero coins) of a full-length prime
of the required form at every `n ≥ n₀`, which is not known. Kept as the deterministic
special case (`FullLength.fullLengthExcept`). -/
def FullLength : Prop :=
  ∀ n (r : G.gen.Coins n), G.n₀ ≤ n → 2 ^ (n - 1) ≤ dlP (G.gen.runAt n [] r)

/-- The generator outputs primes of full length `n` **except on a set of coins of probability
at most `δ n`**: for `n ≥ n₀`, `Pr_r[p < 2^{n−1}] ≤ δ n` (the fallback instance of a strict-PPT
rejection sampler, D10). Used, with `Negligible δ`, by the proofs that divide by `q` or
`p − 1` (Lemma 84.1's range reduction, the `1/q` term of Theorem 107.3): the short-prime coins
are discarded and contribute at most `δ n`. This is a convenience: instances with `p − 1` below
a polynomial can be inverted by exhaustive search, so `hbig` could be dropped (gate 03f1
review, M1; ruling R-03f1-1 (A) keeps it). Whether safe primes (resp. primes `≡ 3 (mod 4)`
with a generator) of full length can be produced for every `n` except with negligible
probability is itself open ([PS10, p. 52]: the sampler's "basic theoretical properties are
unknown"); the hypothesis `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems
records this.

Repair (run-3 audit P8-2): replaces the hypothesis `G.FullLength` of
`fullDLCollection_hardCore` and `elGamal_secure`, which demanded `2^{n−1} ≤ p` on every coin
string and made `{G // G.FullLength}` not known to be inhabited for reasons unrelated to any
cryptographic assumption (contrary to D10 / deviation 15, strict PPT with `2^{-n}` failure). -/
def FullLengthExcept (δ : ℕ → ℝ) : Prop :=
  ∀ n, G.n₀ ≤ n → uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) ≤ δ n

/-- Unfolding `FullLengthExcept`: `G.FullLengthExcept δ` iff for every `n ≥ n₀` the probability
over the generator's coins that `p < 2^{n−1}` is at most `δ n`. -/
theorem fullLengthExcept_iff (δ : ℕ → ℝ) :
    G.FullLengthExcept δ ↔ ∀ n, G.n₀ ≤ n →
      uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) ≤ δ n :=
  Iff.rfl

/-- **The discrete-log experiment** [PS10, Assumption 52.2]:
`Pr[i ← Gen(1^n); x ← Z_m : A(1^n, ⟨i, g^x⟩) = x]`, the average over the generator's coins
of the probability, over the ideal uniform `x ∈ Z_m` and the coins of `A`, that the answer of
`A` decodes to an `n`-bit numeral reading as `x`.

**Deviation:** `A` receives `1^n` and the index (the text's `A(g^x)`); ideal uniform `x`;
`n`-bit answers (module docstring). -/
noncomputable def dlProb (A : NUPPT) (n : ℕ) : ℝ :=
  uexp fun r : G.gen.Coins n =>
    uprob fun z : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
      ∃ x : Fin n → Bool,
        decodeFin n (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ z.1)) z.2) = some x ∧
          bitsToNat x = z.1.val

/-- The defining equation of `dlProb`: `G.dlProb A n` is the average over the generator's coins
`r` of the probability, over `x ∈ Z_m` and the coins of `A`, that `A`'s answer on
`⟨Gen(1^n; r), g^x⟩` decodes to an `n`-bit numeral reading as `x`. -/
theorem dlProb_eq (A : NUPPT) (n : ℕ) :
    G.dlProb A n = uexp fun r : G.gen.Coins n =>
      uprob fun z : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
        ∃ x : Fin n → Bool,
          decodeFin n (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ z.1)) z.2) = some x ∧
            bitsToNat x = z.1.val :=
  rfl

/-- **Discrete-log hardness relative to the generator**: every non-uniform PPT solves the
discrete-log experiment with negligible probability. The safe-prime instance is
[PS10, Assumption 52.2] (`DLAssumption`); the full-group instance is the assumption of
[PS10, Lemma 84.1] (`DiscreteLogHardcore`). -/
def DLHard : Prop := ∀ A : NUPPT, Negligible fun n => G.dlProb A n

/-- Unfolding `DLHard`: `G.DLHard` iff `n ↦ G.dlProb A n` is negligible for every non-uniform
PPT `A`. -/
theorem dlHard_iff : G.DLHard ↔ ∀ A : NUPPT, Negligible fun n => G.dlProb A n := Iff.rfl

/-- The discrete-log probability is nonnegative. -/
theorem dlProb_nonneg (A : NUPPT) (n : ℕ) : 0 ≤ G.dlProb A n := by
  unfold dlProb
  rw [uexp_def]
  exact div_nonneg (Finset.sum_nonneg fun z _ => uprob_nonneg _) (Nat.cast_nonneg _)

/-- The discrete-log probability is at most one. -/
theorem dlProb_le_one (A : NUPPT) (n : ℕ) : G.dlProb A n ≤ 1 := by
  haveI : Nonempty (G.gen.Coins n) := ⟨fun _ => false⟩
  unfold dlProb
  exact (OneWay.uexp_mono fun r => uprob_le_one _).trans (OneWay.uexp_const 1).le

end ExpGroupGen

/-- Full length on every coin string is full length except on a set of probability `0`. -/
theorem ExpGroupGen.FullLength.fullLengthExcept {V : List Bool → Prop} {G : ExpGroupGen V}
    (h : G.FullLength) : G.FullLengthExcept fun _ => 0 := by
  intro n hn
  have hz : uprob (fun r : G.gen.Coins n => dlP (G.gen.runAt n [] r) < 2 ^ (n - 1)) = 0 := by
    rw [← uprob_false (α := G.gen.Coins n)]
    exact OneWay.uprob_congr fun r => ⟨fun hlt => (not_le.mpr hlt (h n r hn)).elim, False.elim⟩
  exact hz.le

/-- A generator of full length on every coin string satisfies the hypothesis
`∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems (with `δ = 0`). -/
theorem ExpGroupGen.FullLength.exists_fullLengthExcept {V : List Bool → Prop} {G : ExpGroupGen V}
    (h : G.FullLength) : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ := by
  refine ⟨fun _ => 0, (negligible_iff _).2 fun c => ⟨1, fun n hn => ?_⟩, h.fullLengthExcept⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [abs_zero]
  positivity

/-! ## The exponentiation collection of an instance generator -/

/-- The fixed valid instance `⟨p, ⟨m, g⟩⟩ = ⟨3, ⟨2, 2⟩⟩` with `2`-bit numerals (`2` has order
`2` in `Z_3`): the index output by the collection's generator below the threshold `n₀` of the
instance generator, where the latter's outputs are unconstrained.

Repair (run-3 audit P3-1): `Collection.sample_spec` requires the sampler's outputs to decode
at *every* generated index, so the collection's generator must output valid indices at every
parameter. -/
def dlDefaultIndex : List Bool :=
  pairEncode (natToList 2 3) (pairEncode (natToList 2 2) (natToList 2 2))

/-- The default index is valid: `3` is prime, `0 < 2 < 3`, and `2` has order `2` in `Z_3`. -/
theorem expValid_dlDefaultIndex : ExpValid dlDefaultIndex := by
  have h3 : dlP dlDefaultIndex = 3 := by
    simp [dlP, dlDefaultIndex, listToNat_natToList (by norm_num : 3 < 2 ^ 2)]
  have h2 : dlM dlDefaultIndex = 2 := by
    simp [dlM, dlDefaultIndex, listToNat_natToList (by norm_num : 2 < 2 ^ 2)]
  have hg : dlG dlDefaultIndex = 2 := by
    simp [dlG, dlDefaultIndex, listToNat_natToList (by norm_num : 2 < 2 ^ 2)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3]; exact Nat.prime_three
  · rw [h2]; norm_num
  · rw [h2, h3]; norm_num
  · rw [hg]; norm_num
  · rw [hg, h3]; norm_num
  · rw [hg, h2, h3]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)

/-- The string function of the collection's index generator on the raw layout
`⟨⟨⟨1^n, []⟩, α⟩, r⟩`: `⟨Gen(1^n; r), []⟩` (no trapdoor) from the threshold `n₀` on, and
`⟨dlDefaultIndex, []⟩` below it (where the instance generator's outputs are unconstrained;
run-3 audit P3-1). -/
def expGenFun {V : List Bool → Prop} (G : ExpGroupGen V) (z : List Bool) : List Bool :=
  if G.n₀ ≤ (NUPPT.inParam z).length then
    pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) []
  else pairEncode dlDefaultIndex []

/-- The raw index generator pairs the instance generator's output with the empty trapdoor
when the parameter length is at least `G.n₀`, and otherwise pairs `dlDefaultIndex` with it:
`expGenFun G z = if G.n₀ ≤ u.length then pairEncode o [] else pairEncode dlDefaultIndex []`,
where `u = NUPPT.inParam z` and `o = G.gen.output (NUPPT.layout u [] [] (NUPPT.inCoins z))`. -/
theorem expGenFun_eq {V : List Bool → Prop} (G : ExpGroupGen V) (z : List Bool) :
    expGenFun G z =
      if G.n₀ ≤ (NUPPT.inParam z).length then
        pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) []
      else pairEncode dlDefaultIndex [] := rfl

/-- The index generator's string function is polynomial-time: the threshold test compares
the length of `1^n` with the constant `1^{n₀}` (`polyTimeComputable_lenLe`), then
`polyTimeComputable_ite` between the instance generator's output and a constant. -/
theorem expGenFun_poly {V : List Bool → Prop} (G : ExpGroupGen V) : PolyTimeComputable (expGenFun G) := by
  have hp : PolyTimeComputable fun z => [decide (G.n₀ ≤ (NUPPT.inParam z).length)] := by
    have h := polyTimeComputable_lenLe.comp
      (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const (List.replicate G.n₀ true)))
    convert h using 1
    funext z
    simp [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hf : PolyTimeComputable fun z =>
      pairEncode (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))) [] :=
    (G.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam (polyTimeComputable_const []) (polyTimeComputable_const [])
      NUPPT.polyTimeComputable_inCoins)).pairEncode (polyTimeComputable_const [])
  have h := polyTimeComputable_ite hp hf (polyTimeComputable_const (pairEncode dlDefaultIndex []))
  convert h using 1
  funext z
  simp only [expGenFun, decide_eq_true_eq]

/-- The index generator of the collection: `Gen(1^n) = ⟨i, []⟩` with `i` the output of the
instance generator (from `n₀` on; `dlDefaultIndex` below), same coins. -/
noncomputable def expGen {V : List Bool → Prop} (G : ExpGroupGen V) : NUPPT :=
  NUPPT.ofPolyTimeUniform (expGenFun_poly G) G.gen.coins

/-- The collection's generator has the coins of the instance generator:
`(expGen G).coins = G.gen.coins`. -/
theorem expGen_coins {V : List Bool → Prop} (G : ExpGroupGen V) :
    (expGen G).coins = G.gen.coins := by
  unfold expGen
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- The coin length of the collection's generator is the instance generator's:
`(expGen G).coinLen n = G.gen.coinLen n`. -/
theorem expGen_coinLen {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) :
    (expGen G).coinLen n = G.gen.coinLen n := by
  rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, expGen_coins]

/-- **The coins of the collection's generator are the instance generator's**: the published
equivalence `(expGen G).Coins n ≃ G.gen.Coins n` (`NUPPT.coinsCongr` along `expGen_coins`), the
interface between the averages over the collection's coins (`Collection.HardCore`,
`SampleClose`, `invProbAt`) and those over `G.gen`'s (`dlProb`, `FullLengthExcept`). -/
noncomputable def expGen_coinsEquiv {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) :
    (expGen G).Coins n ≃ G.gen.Coins n :=
  NUPPT.coinsCongr (expGen_coins G) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (expGen_coinsEquiv G n r) = List.ofFn r`. -/
theorem expGen_coinsEquiv_ofFn {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ)
    (r : (expGen G).Coins n) : List.ofFn (expGen_coinsEquiv G n r) = List.ofFn r :=
  NUPPT.coinsCongr_ofFn (expGen_coins G) n r

/-- **The coin equivalence carries the uniform distribution**: for `P` on `G.gen`'s coins,
`Pr_{r ← (expGen G).Coins n}[P (φ r)] = Pr_{r'}[P r']` with `φ = expGen_coinsEquiv G n`
(`uprob_comp_equiv`). -/
theorem expGen_coinsEquiv_uprob {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ)
    (P : G.gen.Coins n → Prop) :
    uprob (fun r : (expGen G).Coins n => P (expGen_coinsEquiv G n r)) = uprob P :=
  uprob_comp_equiv _ P

/-- **The coin equivalence carries averages**: for `F` on `G.gen`'s coins,
`E_{r ← (expGen G).Coins n}[F (φ r)] = E_{r'}[F r']` with `φ = expGen_coinsEquiv G n`
(`HardcoreBit.uexp_comp_equiv`). -/
theorem expGen_coinsEquiv_uexp {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ)
    (F : G.gen.Coins n → ℝ) :
    uexp (fun r : (expGen G).Coins n => F (expGen_coinsEquiv G n r)) = uexp F :=
  HardcoreBit.uexp_comp_equiv _ F

/-- The activation of the collection's generator: `⟨Gen(1^n; φ r), []⟩` for `n ≥ n₀`,
`⟨dlDefaultIndex, []⟩` below, with the coins read through `φ = expGen_coinsEquiv G n`. -/
theorem expGen_runAt {V : List Bool → Prop} (G : ExpGroupGen V) (n : ℕ) (r : (expGen G).Coins n) :
    (expGen G).runAt n [] r =
      if G.n₀ ≤ n then pairEncode (G.gen.runAt n [] (expGen_coinsEquiv G n r)) []
      else pairEncode dlDefaultIndex [] := by
  rw [NUPPT.runAt_eq, NUPPT.runAt_eq, expGen_coinsEquiv_ofFn, NUPPT.Uniform.runAtL_eq G.gen_uniform]
  unfold expGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [expGenFun, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, NUPPT.layout_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- **Rejection sampling of a number below `m`** from a coin list: `T` trials, trial `t`
reading the first `k` bits of the `t`-th block of `B` bits as a number `v`, accepted iff
`v < m`; `none` if every trial is rejected. With `k` the bit length of `m` the acceptance rate
is `m / 2^k ≥ 1/2` [PS10, Theorem 52.3, "it is easy to sample the domain `D_i`"]. -/
def sampleBelowL (m k B T : ℕ) (r : List Bool) : Option ℕ :=
  (List.range T).findSome? fun t =>
    if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
    else none

/-- `sampleBelowL` is block rejection sampling with the test `v < m`:
`sampleBelowL m k B T = rejectBlocksL (· < m) k B T` (the same blocks, the same test; gate 03f1
review, M2). -/
theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) :
    sampleBelowL m k B T = rejectBlocksL (· < m) k B T := by
  funext r
  rw [rejectBlocksL_eq]
  rfl

/-- A sampled value is below `m`. -/
theorem sampleBelowL_lt {m k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleBelowL m k B T r = some v) :
    v < m := by
  unfold sampleBelowL at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, t, _, _, ht, _⟩ := h
  split_ifs at ht with hc
  rw [Option.some.injEq] at ht
  exact ht ▸ hc

/-- **The rejection sampler is close to uniform** (D10; lemma C4 of the Chapter 2 inventory for
`sampleBelowL`): for `0 < m < 2^n`, `n` trials reading `k = Nat.size m` bits from each of `n`
blocks of `n` uniform coins, with the fallback `0`, output a number within statistical
distance `(1/2)^n` of the uniform number below `m`. The closeness fact behind
`expCollection_sampleClose` and the El Gamal samplers (`egUnit`, `egGenParts`, `egEncParts`,
`ddhExpo`).

**Proof sketch.** A corollary of `statClose_rejectBlocksL` (gate 03f1 review, M2; that lemma is
filled first, and this one is not filled a second time). With `k = Nat.size m`, `k ≤ n` by
`Nat.size_le` (`m < 2^n`), and `sampleBelowL m k n n = rejectBlocksL (· < m) k n n`
(`sampleBelowL_eq_rejectBlocksL`). `statClose_rejectBlocksL (· < m) k n n` with the default
`d = 0` (`0 < m`, `0 < 2^k`) gives closeness `(1 − Pr_{v < 2^k}[v < m])^n = (1 − m/2^k)^n` to
the uniform element of `{v : Fin (2^k) // v < m}`, and `(1 − m/2^k)^n ≤ (1/2)^n` since
`2^k ≤ 2m` (`Nat.lt_size_self` and the minimality of `Nat.size`: `m/2^k ≥ 1/2`). Transport the
target along the value-preserving bijection `{v : Fin (2^k) // v < m} ≃ Fin m`
(`StatClose.comp_equiv_right`) and weaken the bound (`StatClose.mono`). -/
theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
    StatClose (fun b : Fin (n * n) → Bool => (sampleBelowL m (Nat.size m) n n (List.ofFn b)).getD 0)
      (fun x : Fin m => (x : ℕ)) ((1 / 2 : ℝ) ^ n) := by
  have hkn : Nat.size m ≤ n := Nat.size_le.2 hmn
  have hmk : m < 2 ^ Nat.size m := Nat.lt_size_self m
  -- `2^k ≤ 2m`: the top bit of `m` is bit `k − 1`
  have hk2 : 2 ^ Nat.size m ≤ 2 * m := two_pow_size_le_two_mul hm
  -- the block sampler with the test `v < m` and the default `0`
  have h := statClose_rejectBlocksL (· < m) (Nat.size m) n n hkn (d := 0) hm
    (Nat.pow_pos two_pos)
  -- the uniform element of `{v < 2^k | v < m}` is the uniform element of `Fin m`
  let e : Fin m ≃ {v : Fin (2 ^ Nat.size m) // (v : ℕ) < m} :=
    { toFun := fun x => ⟨⟨x.val, lt_trans x.2 hmk⟩, x.2⟩
      invFun := fun v => ⟨v.1.val, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h' := h.comp_equiv_right e
  -- the acceptance probability is `m / 2^k ≥ 1/2`
  have hacc : uprob (fun v : Fin (2 ^ Nat.size m) => (v : ℕ) < m) = m / 2 ^ Nat.size m := by
    rw [← uprob_comp_equiv (bitsEquiv (Nat.size m)) (fun v : Fin (2 ^ Nat.size m) => (v : ℕ) < m)]
    simp only [bitsEquiv_val]
    exact uprob_bitsToNat_lt hmk.le
  rw [hacc] at h'
  have hpow : (1 - (m : ℝ) / 2 ^ Nat.size m) ^ n ≤ (1 / 2 : ℝ) ^ n := by
    rw [← uprob_rejectionSample_none m (Nat.size m) n hm hmk.le]
    exact uprob_rejectionSample_none_le_half_pow m (Nat.size m) n hm hmk.le hk2
  rw [sampleBelowL_eq_rejectBlocksL]
  exact h'.mono hpow

/-- The string function of the domain sampler on the raw layout `⟨⟨⟨1^n, i⟩, α⟩, r⟩`: a number
below the order `m` read from the index, by rejection over `n` trials of `n`-bit blocks
(reading the bit length of `m` from each block), written as a numeral of the index width;
the fallback `0` on failure. -/
def expSampleRaw (z : List Bool) : List Bool :=
  natToList (dlW (NUPPT.inArg z))
    ((sampleBelowL (dlM (NUPPT.inArg z)) (Nat.size (dlM (NUPPT.inArg z)))
      (NUPPT.inParam z).length (NUPPT.inParam z).length (NUPPT.inCoins z)).getD 0)

/-- The raw exponent sampler writes the result of `sampleBelowL m (Nat.size m) n n r`,
with fallback zero, at the width of the input index:
`expSampleRaw z = natToList (dlW i) ((sampleBelowL m (Nat.size m) n n r).getD 0)`, where
`i = NUPPT.inArg z`, `m = dlM i`, and `n` and `r` are the input parameter length and coins. -/
theorem expSampleRaw_eq (z : List Bool) :
    expSampleRaw z =
      natToList (dlW (NUPPT.inArg z))
        ((sampleBelowL (dlM (NUPPT.inArg z)) (Nat.size (dlM (NUPPT.inArg z)))
          (NUPPT.inParam z).length (NUPPT.inParam z).length (NUPPT.inCoins z)).getD 0) := rfl

/-! ### The comparison test of the domain sampler (helper of `polyTimeComputable_expSampleRaw`) -/

/-- The comparison test on a pair `⟨w, b⟩`: not `⟦w⟧ ≤ ⟦b⟧`, i.e. the trial value is below `⟦w⟧`. -/
private def dla_belowAcc (x : List Bool) : Bool :=
  !decide (listToNat (pairFstD x) ≤ listToNat (pairSndD x))

/-- The comparison test is polynomial-time (`ArithmeticFP.le_poly`, `polyTimeComputable_not`). -/
private theorem dla_belowAcc_poly (H : ArithmeticFP) :
    PolyTimeComputable fun x => [dla_belowAcc x] :=
  polyTimeComputable_not (H.le_poly polyTimeComputable_pairFstD polyTimeComputable_pairSndD)

/-- The comparison test decides `⟦b⟧ < ⟦w⟧` on `⟨w, b⟩`. -/
private theorem dla_belowAcc_spec (w b : List Bool) :
    dla_belowAcc (pairEncode w b) = decide (listToNat b < listToNat w) := by
  rw [dla_belowAcc, pairFstD_pairEncode, pairSndD_pairEncode, ← decide_not, decide_eq_decide,
    Nat.not_le]

/-! ### The domain sampler and the collection -/

/-- **The domain sampler is polynomial-time** [PS10, Theorem 52.3, "it is easy to sample the
domain `D_i`"] given the arithmetic bundle.

**Proof sketch.** The bit length `Nat.size m` is the length of the numeral of `m` with its
leading zeros stripped (`H.size`). The sampler is `sampleBelowL m k n n = rejectBlocksL (· < m)
k n n` (`sampleBelowL_eq_rejectBlocksL`), an instance of the block-rejection host H15
(`polyTimeComputable_rejectBlocksL`): the test `v < m` on `⟨⟦m⟧, v⟩` is `H.le`, negated; the
parameter word is the middle numeral `⟦m⟧` of the index, the width word `1^k = sizeStr ⟦m⟧`, and
`1^n` serves as both the block-length and the trial-count word. H15 returns a polynomial-time `g`
whose output is `[]` when every trial is rejected and otherwise has a tail reading as the accepted
value; so the tail of `g z` (`polyTimeComputable_tail`, `List.drop_one`) reads as the sampler's
value with the fallback `0` (the empty tail reads `0`). The output is the last `|p|` bits of
`⟦0⟧_{|p|} ++ t` for that tail `t`, with `⟦0⟧_{|p|} = ⟦p − p⟧_{|p|}` (`H.sub`,
`polyTimeComputable_pairDropPoly`, `PolyTimeComputable.append`): the `|p|`-bit numeral of the
value, also when it is `≥ 2^{|p|}` (`natToList_zero_append_drop`). -/
theorem polyTimeComputable_expSampleRaw (H : ArithmeticFP) : PolyTimeComputable expSampleRaw := by
  -- the middle numeral `⟦m⟧` of the index
  have hms : PolyTimeComputable fun z => pairFstD (pairSndD (NUPPT.inArg z)) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg)
  -- host H15 with the test `v < ⟦m⟧`: width `|sizeStr ⟦m⟧| = Nat.size ⟦m⟧`, `n` blocks of `n` coins
  obtain ⟨g, hg, hs⟩ := polyTimeComputable_rejectBlocksL (fun a v => v < a) (dla_belowAcc_poly H)
    dla_belowAcc_spec hms (H.size.comp hms) NUPPT.polyTimeComputable_inParam
    NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inCoins
  -- the accepted value's word (the payload's tail), `[]` on failure
  have hb : PolyTimeComputable fun z => (g z).tail :=
    (PolyTimeComputable.comp' polyTimeComputable_tail hg).congr fun z => List.drop_one
  -- the numeral of `0` at the index width, `⟦p − p⟧_{|p|}` (`H.sub`)
  have hp : PolyTimeComputable fun z => pairFstD (NUPPT.inArg z) :=
    polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hz := H.sub.comp (hp.pairEncode hp)
  -- width normalization: the last `|p|` bits of `⟦0⟧_{|p|} ++ payload`
  have hq := (polyTimeComputable_pairDropPoly .var).comp (hb.pairEncode (hz.append hb))
  refine hq.congr fun z => ?_
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var,
    subStr_pairEncode, Nat.sub_self]
  rw [natToList_zero_append_drop]
  unfold expSampleRaw dlW
  congr 1
  rw [dlM_eq, ← length_sizeStr, sampleBelowL_eq_rejectBlocksL,
    show rejectBlocksL (· < listToNat (pairFstD (pairSndD (NUPPT.inArg z))))
        (sizeStr (pairFstD (pairSndD (NUPPT.inArg z)))).length (NUPPT.inParam z).length
        (NUPPT.inParam z).length (NUPPT.inCoins z) =
      if g z = [] then none else some (listToNat (g z).tail) from (hs z).2]
  split_ifs with he
  · rw [he, List.tail_nil, listToNat_nil]
    rfl
  · rfl

/-- **The domain sampler** of the exponentiation collection: a uniform `NUPPT` with `n · n`
coins. -/
noncomputable def expSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_expSampleRaw H) (.mul .var .var)

/-- The activation of the domain sampler on the index `i`. -/
theorem expSampler_runAt (H : ArithmeticFP) (n : ℕ) (i : List Bool) (s : (expSampler H).Coins n) :
    (expSampler H).runAt n i s =
      natToList (dlW i) ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s)).getD 0) := by
  rw [NUPPT.runAt_eq]
  unfold expSampler
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [expSampleRaw, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- **The domain sampler's outputs decode and evaluate honestly** (the clause `sample_spec` of
`Collection`, [PS10, Definition 41.1 (2)]; repair of the run-3 audit, P3-1): at every parameter
the generated index is valid — `hV` with `G.valid` from `n₀` on, `expValid_dlDefaultIndex`
below (`expGen_runAt`) — so the domain is `Z_m` with `0 < m < p < 2^{dlW i}`
(`expOrd_of_valid`, `dlP_lt_two_pow`); the sampler outputs `natToList (dlW i) v` with `v < m`
(`expSampler_runAt`, `sampleBelowL_lt`, or the fallback `0`), which `expDec` reads back
(`length_natToList`, `listToNat_natToList`) as `x = (v : Z_m)` with `expEnc i x` the same
numeral (`ZMod.val_natCast`, `Nat.mod_eq_of_lt`); `expEval_spec` gives the evaluator clause.

**Proof sketch.** Case split on `G.n₀ ≤ n` in `expGen_runAt`, then the computation above. -/
theorem expSampler_spec {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : (expGen G).Coins n) (s : (expSampler H).Coins n) :
    ∃ x, expDec (pairFstD ((expGen G).runAt n [] r))
        ((expSampler H).runAt n (pairFstD ((expGen G).runAt n [] r)) s) = some x ∧
      expEval (pairEncode (pairFstD ((expGen G).runAt n [] r))
        ((expSampler H).runAt n (pairFstD ((expGen G).runAt n [] r)) s)) = expF _ x := by
  -- the generated index is valid at every parameter
  have hvalid : ExpValid (pairFstD ((expGen G).runAt n [] r)) := by
    rw [expGen_runAt]
    split_ifs with hn
    · rw [pairFstD_pairEncode]
      exact hV _ (G.valid n _ hn)
    · rw [pairFstD_pairEncode]
      exact expValid_dlDefaultIndex
  generalize pairFstD ((expGen G).runAt n [] r) = i at hvalid ⊢
  rw [expSampler_runAt]
  -- the sampled value `v` is below `m` (accepted, or the fallback `0 < m`)
  set v := (sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s)).getD 0 with hvdef
  have hv : v < dlM i := by
    rcases hs : sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s) with _ | w
    · rw [hvdef, hs, Option.getD_none]
      exact ((expValid_iff i).1 hvalid).2.1
    · rw [hvdef, hs, Option.getD_some]
      exact sampleBelowL_lt hs
  have hvo : v < expOrd i := (expOrd_of_valid hvalid).symm ▸ hv
  -- `x = (v : Z_m)` is encoded by the same numeral
  have henc : expEnc i ((v : ℕ) : ZMod (expOrd i)) = natToList (dlW i) v := by
    rw [expEnc_eq, ZMod.val_natCast, Nat.mod_eq_of_lt hvo]
  refine ⟨((v : ℕ) : ZMod (expOrd i)), ?_, ?_⟩
  · rw [← henc, expDec_expEnc]
  · rw [← henc, expEval_spec]

/-- **The exponentiation collection of an instance generator**: indices `⟨p, ⟨m, g⟩⟩`,
domains `D_i = Z_m` (valid indices; `Z_1` otherwise), `f_i(x) = g^x mod p`, the generator
`expGen G` (the instance generator from `n₀` on, `dlDefaultIndex` below), the sampler
`expSampler H` and the evaluator `expEval` (one modular exponentiation); the validity bridge
`hV` makes every generated index valid, so that the sampler's outputs decode
(`expSampler_spec`, run-3 audit P3-1). The collection `DL` of [PS10, Theorem 52.3] is the
safe-prime instance `dlCollection`; the full-group collection of [PS10, Lemma 84.1] is the
instance of `DiscreteLogHardcore`. -/
noncomputable def expCollection {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) : Collection where
  D i := ZMod (expOrd i)
  encD := expEnc
  decD := expDec
  decD_encD := expDec_expEnc
  encD_decD _ _ _ := expEnc_of_expDec
  f := expF
  gen := expGen G
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := expSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval := expEval
  eval_poly := polyTimeComputable_expEval H
  eval_spec := expEval_spec
  sample_spec := expSampler_spec H G hV

/-- **The domain of the exponentiation collection is `Z_m`**: the published equivalence
`(expCollection H G hV).D i ≃ ZMod (expOrd i)` (the identity). It is the interface to the
domain: elements of `D i` are read through it (`expCollection_f`, `expCollection_encD`,
`expCollection_decD`), so no statement needs the collection to reduce at the type level, and
uniform statements over `D i` transport along it (`uprob_comp_equiv`,
`StatClose.comp_equiv_right`). -/
def expCollection_domEquiv {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool) :
    (expCollection H G hV).D i ≃ ZMod (expOrd i) :=
  Equiv.refl _

/-- **The domain equivalence carries the uniform distribution**: for `P` on `Z_m`,
`Pr_{x ← D i}[P (φ x)] = Pr_y[P y]` with `φ = expCollection_domEquiv H G hV i` (`uprob_comp_equiv`),
the form in which uniform statements over the domain are read. -/
theorem expCollection_domEquiv_uprob {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool)
    (P : ZMod (expOrd i) → Prop) :
    uprob (fun x : (expCollection H G hV).D i => P (expCollection_domEquiv H G hV i x)) = uprob P :=
  uprob_comp_equiv _ P

/-- The function of the exponentiation collection is `expF`, read through the domain
equivalence: `(expCollection H G hV).f i x = expF i (expCollection_domEquiv H G hV i x)`. -/
theorem expCollection_f {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool) (x : (expCollection H G hV).D i) :
    (expCollection H G hV).f i x = expF i (expCollection_domEquiv H G hV i x) := rfl

/-- The encoder of the exponentiation collection is `expEnc`, read through the domain
equivalence: `(expCollection H G hV).encD i x = expEnc i (expCollection_domEquiv H G hV i x)`. -/
theorem expCollection_encD {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool) (x : (expCollection H G hV).D i) :
    (expCollection H G hV).encD i x = expEnc i (expCollection_domEquiv H G hV i x) := rfl

/-- The decoder of the exponentiation collection is `expDec`, carried back along the domain
equivalence:
`(expCollection H G hV).decD i w = (expDec i w).map (expCollection_domEquiv H G hV i).symm`. -/
theorem expCollection_decD {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i w : List Bool) :
    (expCollection H G hV).decD i w = (expDec i w).map (expCollection_domEquiv H G hV i).symm := by
  show expDec i w = _
  cases expDec i w <;> rfl

/-- The index generator of the exponentiation collection is `expGen G`. -/
theorem expCollection_gen {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) : (expCollection H G hV).gen = expGen G := rfl

/-- The domain sampler of the exponentiation collection is `expSampler H`. -/
theorem expCollection_sample {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) : (expCollection H G hV).sample = expSampler H := rfl

/-- The evaluator of the exponentiation collection is `expEval`. -/
theorem expCollection_eval {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) : (expCollection H G hV).eval = expEval := rfl

/-- **The coins of the exponentiation collection's generator are the instance generator's**:
the published equivalence `(expCollection H G hV).gen.Coins n ≃ G.gen.Coins n`
(`expGen_coinsEquiv`), through which the collection's averages are read as averages over
`G.gen`'s coins (`expCollection_coinsEquiv_uprob`, `expCollection_coinsEquiv_uexp`). -/
noncomputable def expCollection_coinsEquiv {V : List Bool → Prop} (H : ArithmeticFP)
    (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) :
    (expCollection H G hV).gen.Coins n ≃ G.gen.Coins n :=
  expGen_coinsEquiv G n

/-- The collection's coin equivalence carries the uniform distribution:
`Pr_r[P (φ r)] = Pr_{r'}[P r']` with `φ = expCollection_coinsEquiv H G hV n`. -/
theorem expCollection_coinsEquiv_uprob {V : List Bool → Prop} (H : ArithmeticFP)
    (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) (P : G.gen.Coins n → Prop) :
    uprob (fun r : (expCollection H G hV).gen.Coins n => P (expCollection_coinsEquiv H G hV n r)) =
      uprob P :=
  uprob_comp_equiv _ P

/-- The collection's coin equivalence carries averages:
`E_r[F (φ r)] = E_{r'}[F r']` with `φ = expCollection_coinsEquiv H G hV n`. -/
theorem expCollection_coinsEquiv_uexp {V : List Bool → Prop} (H : ArithmeticFP)
    (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i) (n : ℕ) (F : G.gen.Coins n → ℝ) :
    uexp (fun r : (expCollection H G hV).gen.Coins n => F (expCollection_coinsEquiv H G hV n r)) =
      uexp F :=
  HardcoreBit.uexp_comp_equiv _ F

/-- The index generated by the exponentiation collection from `n₀` on is the instance
generator's output on the coins read through `expCollection_coinsEquiv`. -/
theorem expCollection_index {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : (expCollection H G hV).gen.Coins n)
    (hn : G.n₀ ≤ n) :
    (expCollection H G hV).index n r = G.gen.runAt n [] (expCollection_coinsEquiv H G hV n r) := by
  rw [Collection.index_eq]
  exact (congrArg pairFstD (expGen_runAt G n r)).trans (by rw [if_pos hn, pairFstD_pairEncode]; rfl)

/-- The index generated by the exponentiation collection below `n₀` is the default index. -/
theorem expCollection_index_of_lt {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (n : ℕ) (r : (expCollection H G hV).gen.Coins n)
    (hn : n < G.n₀) :
    (expCollection H G hV).index n r = dlDefaultIndex := by
  rw [Collection.index_eq]
  exact (congrArg pairFstD (expGen_runAt G n r)).trans
    (by rw [if_neg (not_le.mpr hn), pairFstD_pairEncode])

/-- The domain of the exponentiation collection at an index is `Z_{expOrd i}`. -/
theorem expCollection_D {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (i : List Bool) :
    (expCollection H G hV).D i = ZMod (expOrd i) := rfl

/-- **The decoded domain sampler is `(1/2)^n`-close to uniform on `Z_m`** at a valid index of
width `n`: `statClose_sampleBelowL` on the sampler's `n · n` coins (read through
`NUPPT.coinsEquivPoly`), mapped through the decoder, which reads the numeral back exactly.

**Proof sketch.** At a valid index of width `n`, `0 < m` and `m < p < 2^n`. Identify the
sampler's coins with `Fin (n · n) → Bool` (`NUPPT.coinsEquivPoly`, `finCongr`; the coin list is
unchanged, `NUPPT.coinsEquivPoly_ofFn`) and `Z_m` with `Fin m` by the value map. Then
`statClose_sampleBelowL`, moved along the coin identification (`StatClose.comp_equiv_left`),
mapped through `v ↦ expDec i ⟦v⟧_n` (`StatClose.map`) and moved along `Z_m ≃ Fin m`
(`StatClose.comp_equiv_right`), is the claim: its left side is the decoded sampler output
(`expSampler_runAt`), and on its right side `expDec i ⟦y.val⟧_n = some y` (`expEnc_eq`,
`expDec_expEnc`). -/
private theorem dla_statClose_expDec (H : ArithmeticFP) {n : ℕ} {i : List Bool} (hv : ExpValid i)
    (hw : dlW i = n) :
    StatClose (fun s : (expSampler H).Coins n => expDec i ((expSampler H).runAt n i s))
      (fun x : ZMod (expOrd i) => some x) ((1 / 2 : ℝ) ^ n) := by
  have hv' := (expValid_iff i).1 hv
  have hm : 0 < dlM i := hv'.2.1
  have hmn : dlM i < 2 ^ n := hw ▸ hv'.2.2.1.trans (dlP_lt_two_pow i)
  have hord : expOrd i = dlM i := expOrd_of_valid hv
  -- the sampler's coins are `n · n` bits
  have hcoins : (expSampler H).coins = .mul .var .var := by
    unfold expSampler
    exact NUPPT.coins_ofPolyTimeUniform _ _
  have hlen : (PolyExpr.mul .var .var).eval n = n * n := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_var]
  let e : (expSampler H).Coins n ≃ (Fin (n * n) → Bool) :=
    (NUPPT.coinsEquivPoly hcoins n).trans (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool))
  have hofn : ∀ s, List.ofFn (e s) = List.ofFn s := by
    intro s
    rw [← NUPPT.coinsEquivPoly_ofFn hcoins n s]
    exact (List.ofFn_congr hlen.symm _).trans rfl
  -- the residues below `m` are the elements of `Z_m`
  let e2 : ZMod (expOrd i) ≃ Fin (dlM i) :=
    { toFun := fun y => ⟨y.val, lt_of_lt_of_eq (ZMod.val_lt y) hord⟩
      invFun := fun x => ((x : ℕ) : ZMod (expOrd i))
      left_inv := fun y => ZMod.natCast_zmod_val y
      right_inv := fun x => Fin.ext (by
        show ((x : ℕ) : ZMod (expOrd i)).val = x
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_eq x.2 hord.symm)]) }
  let g : ℕ → Option (ZMod (expOrd i)) := fun v => expDec i (natToList (dlW i) v)
  have h := (((statClose_sampleBelowL hm hmn).comp_equiv_left e).map g).comp_equiv_right e2
  have hX : (fun s : (expSampler H).Coins n =>
      g ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn (e s))).getD 0)) =
      fun s => expDec i ((expSampler H).runAt n i s) := by
    funext s
    rw [hofn, expSampler_runAt]
  have hY : (fun y : ZMod (expOrd i) => g ((e2 y : Fin (dlM i)) : ℕ)) = fun y => some y := by
    funext y
    show expDec i (natToList (dlW i) y.val) = some y
    rw [← expEnc_eq, expDec_expEnc]
  rw [hX, hY] at h
  exact h

/-- **The domain sampler is close to uniform** [PS10, Theorem 52.3, "it is easy to sample the
domain `D_i`"]: the decoded output of `expSampler` at a generated index is within a
negligible statistical distance of the uniform element of `Z_m`.

**Proof sketch.** Take `δ n := 1` for `n < n₀` and `δ n := (1/2)^n` for `n ≥ n₀`. At a
generated index `i` (`expCollection_index`, valid by `hV ∘ G.valid`, well formed with
`dlW i = n`) the sampler outputs `natToList n (sampleBelowL m k n n r).getD 0` with
`m = dlM i = expOrd i` (`expSampler_runAt`, `expOrd_of_valid`) and `k = Nat.size m ≤ n`
(`Nat.size_le`, `m < p < 2^n`): `n` trials each reading `k` uniform bits of a block of the
coins (`uprob_comp_equiv` on the block decomposition `NumberTheory.chunk`), accepted iff the
value is below `m`; `sampleBelowL` is `firstHit (· < m)` of the numbers read from the blocks
(`List.findSome?` over `List.range`), so `statClose_sampleBelowL` (`statClose_firstHit` on
`Fin (2^k)` transported along `bitsEquiv`) gives closeness `(1 - m/2^k)^n ≤ (1/2)^n`
(`Nat.lt_size_self`: `m/2^k ≥ 1/2`), and the decoder `expDec` reads the numeral back exactly
(`listToNat_natToList`, `StatClose.map`, `ZMod.natCast_zmod_val`). Negligibility by
`negligible_two_pow_neg` and `Negligible.mono`. -/
theorem expCollection_sampleClose {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (expCollection H G hV).SampleClose δ := by
  refine ⟨fun n => if n < G.n₀ then 1 else (1 / 2 : ℝ) ^ n, ?_, ?_⟩
  · refine negligible_two_pow_neg.mono ⟨G.n₀, fun n hn => ?_⟩
    rw [if_neg (not_lt.2 hn), one_div]
  · rw [Collection.sampleClose_iff]
    intro n r
    by_cases hn : n < G.n₀
    · rw [if_pos hn]
      exact statClose_one _ _
    rw [if_neg hn]
    have hn' : G.n₀ ≤ n := not_lt.1 hn
    -- the generated index is valid and of width `n`
    have hidx := expCollection_index H G hV n r hn'
    have hv : ExpValid ((expCollection H G hV).index n r) := hidx ▸ hV _ (G.valid n _ hn')
    have hw : dlW ((expCollection H G hV).index n r) = n :=
      hidx ▸ (G.wellFormed n _ hn').dlW_eq
    generalize (expCollection H G hV).index n r = j at hv hw ⊢
    rw [expCollection_sample]
    simp only [expCollection_decD]
    have h := ((dla_statClose_expDec H hv hw).map
      (Option.map (expCollection_domEquiv H G hV j).symm)).comp_equiv_right
        (expCollection_domEquiv H G hV j)
    have hY : (fun x : (expCollection H G hV).D j =>
        Option.map (expCollection_domEquiv H G hV j).symm (some (expCollection_domEquiv H G hV j x))) =
        fun x => some x := by
      funext x
      rw [Option.map_some, Equiv.symm_apply_apply]
    rw [hY] at h
    exact h

/-- **An inverter's success is a discrete-log success** at a valid index of width `n`: if `A`'s
answer `w` decodes under `expDec` to a preimage of `g^y`, then `w` is the `n`-bit numeral of `y`
(`expF_injective`). -/
private theorem dla_dl_of_inv {i w : List Bool} {n : ℕ} (hv : ExpValid i) (hw : dlW i = n)
    {y : ZMod (expOrd i)} (h : ∃ x', expDec i w = some x' ∧ expF i x' = expF i y) :
    ∃ x : Fin n → Bool, decodeFin n w = some x ∧ bitsToNat x = y.val := by
  obtain ⟨x', hdec, hf⟩ := h
  obtain rfl := expF_injective hv hf
  rw [expDec] at hdec
  split_ifs at hdec with hc
  obtain ⟨hlen, hlt⟩ := hc
  rw [hw] at hlen
  rw [decodeFin_eq, dif_pos hlen]
  refine ⟨_, rfl, ?_⟩
  rw [bitsToNat_eq_listToNat, ← List.ofFn_congr hlen w.get, List.ofFn_get, ← Option.some.inj hdec,
    ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-- **Inverting the collection is the discrete-log experiment** [PS10, proof of Theorem 52.3,
"the discrete log assumption implies that `f_{p,g}` is hard to invert"]: for `n ≥ n₀`, the
inversion probability of `A` against the exponentiation collection is at most its
discrete-log probability (the same machine, no reduction needed).

**Proof sketch.** Unfold both averages over the generator's coins (`OneWay.uexp_mono`) and
fix `r`; the index `i = Gen(1^n; r)` is valid and well formed (`hV`, `G.valid`,
`G.wellFormed`, `dlW i = n`). If `A`'s answer `w` decodes under `expDec` to `x'` with
`expF i x' = expF i x`, then `x' = x` (`expF_injective`), `w.length = n` and
`listToNat w = x.val`, so `decodeFin n w = some x''` with `bitsToNat x'' = listToNat w = x.val`
(`decodeFin`, `bitsToNat_eq_listToNat`, `List.ofFn_get`); `uprob_mono` with the coin types
identified through `expCollection_coinsEquiv` (`expCollection_index`,
`expCollection_coinsEquiv_uexp`). -/
theorem expCollection_invProbAt_le {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (A : NUPPT) {n : ℕ} (hn : G.n₀ ≤ n) :
    (expCollection H G hV).invProbAt A n ≤ G.dlProb A n := by
  rw [Collection.invProbAt_eq, ExpGroupGen.dlProb_eq]
  refine le_of_le_of_eq (OneWay.uexp_mono fun r => ?_) (expCollection_coinsEquiv_uexp H G hV n _)
  have hv : ExpValid (G.gen.runAt n [] (expCollection_coinsEquiv H G hV n r)) := hV _ (G.valid n _ hn)
  have hw : dlW (G.gen.runAt n [] (expCollection_coinsEquiv H G hV n r)) = n :=
    (G.wellFormed n _ hn).dlW_eq
  rw [expCollection_index H G hV n r hn]
  generalize G.gen.runAt n [] (expCollection_coinsEquiv H G hV n r) = i at hv hw ⊢
  -- read the domain `D i` as `Z_m` (`expCollection_domEquiv`) and compare pointwise
  rw [← uprob_comp_equiv
    (Equiv.prodCongr (expCollection_domEquiv H G hV i).symm (Equiv.refl (A.Coins n)))]
  refine uprob_mono fun z hz => ?_
  obtain ⟨x', hdec, hf⟩ := hz
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply,
    expCollection_f, expCollection_decD, Equiv.apply_symm_apply] at hdec hf
  obtain ⟨x'', hx'', rfl⟩ := Option.map_eq_some_iff.1 hdec
  rw [Equiv.apply_symm_apply] at hf
  exact dla_dl_of_inv hv hw ⟨x'', hx'', hf⟩

/-- **The exponentiation collection is one-way under discrete-log hardness** (the generic
form of [PS10, Theorem 52.3]).

**Proof sketch.** The sampling clause is `expCollection_sampleClose H G hV`. For the
hardness clause fix `A`: `expCollection_invProbAt_le H G hV A` bounds the inversion
probability by `G.dlProb A n` for `n ≥ n₀`, negligible by `hG A`; conclude by
`Negligible.mono` (`Collection.invProbAt_nonneg`, threshold `n₀`). -/
theorem expCollection_oneWay {V : List Bool → Prop} (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (hG : G.DLHard) : (expCollection H G hV).OneWay := by
  refine ⟨expCollection_sampleClose H G hV, fun A => ?_⟩
  refine ((ExpGroupGen.dlHard_iff G).1 hG A).mono ⟨G.n₀, fun n hn => ?_⟩
  rw [abs_of_nonneg (Collection.invProbAt_nonneg _ A n), abs_of_nonneg (G.dlProb_nonneg A n)]
  exact expCollection_invProbAt_le H G hV A hn

/-! ## Safe primes: the discrete-log assumption and the collection `DL` -/

/-- A **safe-prime instance** `⟨p, ⟨q, g⟩⟩`: a valid index whose order `q` is prime with
`p = 2q + 1`, so that `g` generates the subgroup of squares `G_q ≤ Z_p^*` of prime order `q`
[PS10, Assumption 52.2 and p. 52, "the subgroup of squares … has order `q` which is prime"]. -/
def SafePrimeValid (i : List Bool) : Prop :=
  ExpValid i ∧ (dlM i).Prime ∧ dlP i = 2 * dlM i + 1

/-- Unfolding `SafePrimeValid`: `i` is a safe-prime instance iff it is valid, `m` is prime and
`p = 2m + 1`. -/
theorem safePrimeValid_iff (i : List Bool) :
    SafePrimeValid i ↔ ExpValid i ∧ (dlM i).Prime ∧ dlP i = 2 * dlM i + 1 := Iff.rfl

/-- A safe-prime instance is a valid instance. -/
theorem SafePrimeValid.expValid {i : List Bool} (h : SafePrimeValid i) : ExpValid i := h.1

/-- **Safe-prime instance generators**: PPTs `Gen(1^n) = ⟨p, ⟨q, g⟩⟩` outputting safe primes
`p = 2q + 1` of length `n` with a generator `g` of the order-`q` subgroup of squares — the
formal "`q ← Π_n; g ← Gen_{G_q}`" of [PS10, Assumption 52.2] and the "`p ← Π̃_n; y ← Gen_q`"
of [PS10, Assumption 105.1]. -/
abbrev SafePrimeGen : Type 1 := ExpGroupGen SafePrimeValid

/-- **The discrete-log assumption** [PS10, Assumption 52.2] relative to a safe-prime instance
generator `G`: for every non-uniform PPT `A`,
`Pr[(p, q, g) ← Gen(1^n); x ← Z_q : A(1^n, ⟨⟨p, ⟨q, g⟩⟩, g^x⟩) = x]` is negligible.

**Deviation:** `A` receives `1^n` and the instance `(p, q, g)` (the text's `A(g^x)`, source
error 8); the group is the subgroup of squares of `Z_p^*` for a safe prime; the instance law
is the generator's (the text's ideal `q ← Π_n; g ← Gen_{G_q}` has no known efficient
sampler, p. 52); "`< ε(n)`" is "negligible" (module docstring). -/
def DLAssumption (G : SafePrimeGen) : Prop := G.DLHard

/-- Unfolding: the discrete-log assumption is the negligibility of every `dlProb`. -/
theorem dlAssumption_iff (G : SafePrimeGen) :
    DLAssumption G ↔ ∀ A : NUPPT, Negligible fun n => G.dlProb A n := Iff.rfl

/-- **The collection `DL`** [PS10, Theorem 52.3]: indices `(q, g)` (with `p`), domains
`D_i = Z_q`, ranges `R_i = G_q`, `f_{q,g}(x) = g^x`, with the instance generator `G` as
`Gen`, the rejection sampler of `Z_q` and the modular-exponentiation evaluator.

**Deviation:** the text's `R_i = G_p`, `f_{p,g}` are read as `G_q`, `f_{q,g}` (source
error 8) and the parameter `k` as `n`; the range `G_q` is encoded as residues modulo `p`
(`expF`). -/
noncomputable def dlCollection (H : ArithmeticFP) (G : SafePrimeGen) : Collection :=
  expCollection H G fun _ h => h.expValid

/-- **The domain of `DL` is `Z_q`**: the published equivalence
`(dlCollection H G).D i ≃ ZMod (expOrd i)` (the identity), the interface to the domain
(`dlCollection_f`, `dlCollection_encD`, `dlCollection_decD`; see `expCollection_domEquiv`). -/
def dlCollection_domEquiv (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool) :
    (dlCollection H G).D i ≃ ZMod (expOrd i) :=
  expCollection_domEquiv H G (fun _ h => h.expValid) i

/-- **The domain equivalence carries the uniform distribution**: for `P` on `Z_q`,
`Pr_{x ← D i}[P (φ x)] = Pr_y[P y]` with `φ = dlCollection_domEquiv H G i` (`uprob_comp_equiv`),
the form in which uniform statements over the domain are read. -/
theorem dlCollection_domEquiv_uprob (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool)
    (P : ZMod (expOrd i) → Prop) :
    uprob (fun x : (dlCollection H G).D i => P (dlCollection_domEquiv H G i x)) = uprob P :=
  uprob_comp_equiv _ P

/-- The function of `DL` is `expF`, read through the domain equivalence:
`(dlCollection H G).f i x = expF i (dlCollection_domEquiv H G i x)`. -/
theorem dlCollection_f (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool)
    (x : (dlCollection H G).D i) :
    (dlCollection H G).f i x = expF i (dlCollection_domEquiv H G i x) :=
  expCollection_f H G (fun _ h => h.expValid) i x

/-- The encoder of `DL` is `expEnc`, read through the domain equivalence:
`(dlCollection H G).encD i x = expEnc i (dlCollection_domEquiv H G i x)`. -/
theorem dlCollection_encD (H : ArithmeticFP) (G : SafePrimeGen) (i : List Bool)
    (x : (dlCollection H G).D i) :
    (dlCollection H G).encD i x = expEnc i (dlCollection_domEquiv H G i x) :=
  expCollection_encD H G (fun _ h => h.expValid) i x

/-- The decoder of `DL` is `expDec`, carried back along the domain equivalence:
`(dlCollection H G).decD i w = (expDec i w).map (dlCollection_domEquiv H G i).symm`. -/
theorem dlCollection_decD (H : ArithmeticFP) (G : SafePrimeGen) (i w : List Bool) :
    (dlCollection H G).decD i w = (expDec i w).map (dlCollection_domEquiv H G i).symm :=
  expCollection_decD H G (fun _ h => h.expValid) i w

/-- The index generator of `DL` is `expGen G`. -/
theorem dlCollection_gen (H : ArithmeticFP) (G : SafePrimeGen) :
    (dlCollection H G).gen = expGen G :=
  expCollection_gen H G (fun _ h => h.expValid)

/-- The domain sampler of `DL` is `expSampler H`. -/
theorem dlCollection_sample (H : ArithmeticFP) (G : SafePrimeGen) :
    (dlCollection H G).sample = expSampler H :=
  expCollection_sample H G (fun _ h => h.expValid)

/-- The evaluator of `DL` is `expEval`. -/
theorem dlCollection_eval (H : ArithmeticFP) (G : SafePrimeGen) :
    (dlCollection H G).eval = expEval :=
  expCollection_eval H G (fun _ h => h.expValid)

/-- **The coins of `DL`'s generator are the instance generator's**: the published equivalence
`(dlCollection H G).gen.Coins n ≃ G.gen.Coins n` (`expCollection_coinsEquiv`). -/
noncomputable def dlCollection_coinsEquiv (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) :
    (dlCollection H G).gen.Coins n ≃ G.gen.Coins n :=
  expCollection_coinsEquiv H G (fun _ h => h.expValid) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (dlCollection_coinsEquiv H G n r) = List.ofFn r`. -/
theorem dlCollection_coinsEquiv_ofFn (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (dlCollection H G).gen.Coins n) :
    List.ofFn (dlCollection_coinsEquiv H G n r) = List.ofFn r :=
  expGen_coinsEquiv_ofFn G n r

/-- The index generated by `DL` from `n₀` on is the instance generator's output `⟨p, ⟨q, g⟩⟩`
on the coins read through `dlCollection_coinsEquiv`. -/
theorem dlCollection_index (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (dlCollection H G).gen.Coins n) (hn : G.n₀ ≤ n) :
    (dlCollection H G).index n r = G.gen.runAt n [] (dlCollection_coinsEquiv H G n r) :=
  expCollection_index H G _ n r hn

/-- **Theorem 52.3** [PS10, Theorem 52.3]: under the discrete-log assumption (and the
arithmetic hypotheses), `DL` is a collection of one-way functions.

**Deviation:** see `dlCollection` and the module docstring (instance generator, safe primes,
rejection-sampled domain).

**Proof sketch.** `expCollection_oneWay` with `hV := SafePrimeValid.expValid`: the sampler
is close to uniform (`expCollection_sampleClose`) and inverting the collection is the
discrete-log experiment (`expCollection_invProbAt_le`), negligible by `hDL`. -/
theorem dlCollection_oneWay (H : ArithmeticFP) (G : SafePrimeGen) (hDL : DLAssumption G) :
    (dlCollection H G).OneWay :=
  expCollection_oneWay H G (fun _ h => h.expValid) hDL

end TCSlib.Cryptography.Candidates

## ===== policy.md (records, at 4f4a7592a54cf82fa04f96b83645d7936672614c) =====

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

## ===== pack-r1.md (this pack) =====

# Gate 44 · Pairing fills: T1 `bdhAssumption_of_dbdhAssumption` (#340) and T4 `exists_bb1_distinguisher` (#346) · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). This gate audits two
fill PRs of the pairing campaign together, because they merge together and their merged tree is the one the maintainer
replayed.

- **PR #340** (`pair-bdh`, T1): draft [PR #340](https://github.com/Shilun-Allan-Li/tcslib/pull/340) at
  `916afc25c21f5e52b4b01958186ad55d2f615fd1` (branch `fill/pairings-pair-bdh`). One SSH-signed commit on #331's head
  `9e7a96481785d6cac4dea3b2e990c49ac278b060`, which is the merge base with the records branch. It changes
  `Pairing/Assumptions.lean` only (+227/−8). Base `cryptography/pass-shelat-ch2-4` (retargeted after #331 merged).
- **PR #346** (`bb1-machine`, T4): draft [PR #346](https://github.com/Shilun-Allan-Li/tcslib/pull/346) at
  `89a18a8225be1b76166af12a15179da291747783` (branch `land/pairings-bb1-machine`). Seven SSH-signed commits on the merge
  base `7291f6b237fec75add1549c0992c174442180488`: three in-house checkpoints, the external worker's three commits
  (re-signed cherry-picks, authors kept), and the landing edit LE-bb1m. It changes 8 files (+2741/−17).
- **Records pin:** `8f888790b7e40f9e0529967e29a05a72c5ee8ba3`. It descends from the records tip at which the replay was staged,
  `1d1a9bb3aa4d5d28c7c9a2343cb322a39da07821` ("Records: #346 (T4) phase 2 accept; replay on snapshot #4"), which holds both
  maintainer reviews. Every record this pack cites is read at `1d1a9bb3` unless it says otherwise; this pack's own files are
  filed after it. During staging three records-only commits landed (`fc0aa4e1`, `fa8a0529`,
  `8f888790b7e40f9e0529967e29a05a72c5ee8ba3`: the bb1-sim T2/T3 fill staged and dispatched); they change no code path, and
  `8f888790` × #340 × #346 (tree `6ef355bb…`) has T44's code exactly.
- **Lean base.** The records tip's Lean equals `463f224414ab7615e54104be353bfcda9dfceda7` (the merge of #352), which is
  **olean snapshot #4** (map SHA-256 `6607620d725049c90b34a51a2ab891f1520fd0f576aaf3f9d51301222cee41e7`, 1453 files). The diff
  `463f2244..1d1a9bb3` over `TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the lake files and `lean-toolchain` is empty
  (`checks/series.txt`).
- **The merged tree T44** = tip × #340 × #346 = `33681cb8ed893a897ca2028d5ada70ca29237978`. All three merge orders are
  clean and give this tree. Its Lean equals `c7be1301f59ec0f208f2645544abac8ac5cc6626`, the three-way tree that #346's
  phase 2 computed from `463f2244` (0 code paths differ). Against the tip it changes exactly the 9 files of the two PRs,
  each blob-equal to its PR head, and the two PRs share no path (`checks/mergetrees.txt`).
- **Scope:** a **proof audit** of two admitted, frozen statements, the reader insertions that one of them was granted, and
  the joint integration evidence:

  | Target | File · line at T44 | Source |
  |---|---|---|
  | **T1** `BilinearGen.bdhAssumption_of_dbdhAssumption` | `Pairing/Assumptions.lean:426` | folklore (not stated in [BB04] or [Jou00]; ruling Q10); the problems of [BB04, §3.1] |
  | **T4** `exists_bb1_distinguisher` | `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean:104` | [BB04, §4.2, the algorithm `B` in the proof of Theorem 4.1], depth 1 |
  | consumer `bb1_sidSecure` (proved at the base from T2–T4, unchanged) | `IdentityBased/BonehBoyenSecurity.lean:124` | [BB04, Theorem 4.1] at depth 1 |

  T1–T4 passed Gate 40 (closed on round 2, `e008f3a4…`), which judged T1–T4 true and T2–T4 sufficient for `bb1_sidSecure`.
  T2 `bb1_sim_real` and T3 `bb1_sim_random` (`BonehBoyenSecurity.lean:89`, `:104`) remain admitted; they are the bb1-sim
  fill's, not this gate's.

Lean paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/`; `IB/` is
`AdvancedEncryption/IdentityBased/` and `BBM/` is `IB/BonehBoyenMachine/`.

## What changed

Lines are tip → T44 (`source-head-r1.json`; every line is at most 100 characters; no tab or trailing space).

| File | PR | Status | Lines |
|---|---|---|---:|
| `Pairing/Assumptions.lean` | #340 | frozen; T1's body and sketch, 4 imports, 10 private helpers | 221 → 440 |
| `IB/Defs.lean` | #346 | frozen; 3 approved readers (pure insertion) | 433 → 476 |
| `IB/BonehBoyen.lean` | #346 | frozen; 4 approved readers (pure insertion) | 677 → 714 |
| `IB/BonehBoyenMachine.lean` | #346 | frozen; 5 helper imports, a `## Contents` section, T4's body and sketch | 85 → 137 |
| `BBM/Draws.lean` | #346 | new | 451 |
| `BBM/Words.lean` | #346 | new | 632 |
| `BBM/Handler.lean` | #346 | new | 899 |
| `BBM/Reduction.lean` | #346 | new | 243 |
| `BBM/Oracles.lean` | #346 | new | 367 |

No other file changes: `IB/BonehBoyenSecurity.lean` (T2, T3, `bb1_sidSecure`), `Pairing/Group.lean`,
`Pairing/Operations.lean`, `KeyExchange/Joux.lean`, the facades and the root are blob-equal at the tip and at T44
(`checks/headers.txt`).

### #340: T1 (maintainer, in-house, under Seyoon's overnight authorization of 2026-11-16)

**The route** (Gate 40's): `D` re-pairs the first five components of its input into the BDH string, runs the solver `A` with
`A`'s own coins and advice, and outputs `[true]` iff the answer equals the last component.
- `D := NUPPT.ofPolyTime` of the raw layout function (`exists_bdhDistinguisher`); the equality test is
  `polyTimeComputable_pairEq`; the projections are `tupleBdh`/`tupleTgt` (compositions of `pairFstD`/`pairSndD`).
- On `P_BDH`, acceptance equals `A`'s success: coins moved by `coinsCongr` and `expect_sample_equiv`, the unused sample of
  `T` by `expect_const`.
- On `R_BDH`, the samples of `T` and of the coins are exchanged (`expect_sample_comm`); for fixed coins the answer is one
  string, which encodes a uniform `T` with probability at most `1/p` by injectivity of `encT` (`prob_eq_encT_le`).
- `1/p ≤ 2^{-κ} + [p < 2^κ]` pointwise, and the bad generator coins cost at most `δ(κ)` (`orderAtLeastExcept_iff`,
  `prob_sample_eq_uprob`), giving `Pr[A wins] ≤ dbdhAdv D κ + 2^{-κ} + δ(κ)` (`accept_bdhGame_le`). No group operation,
  decoding or `Ops`.

Four imports were added: `Complexity.Randomized.Closure`, `Complexity.Randomized.Repetition`,
`Cryptography.Games.Bridges.Experiments` and `Cryptography.OneWayFunctions.Basic`. The ten new declarations are all
`private`, each with a formula docstring; the two with proofs of 15 lines or more carry a `**Proof sketch.**`. The
in-house REPORT's `## Overlap and reuse` has 7 disclosures (§ 5).

### #346: T4 (in-house checkpoints, then an external Claude worker, then the maintainer's landing edit)

**The route** (Gate 40's, with G40-03's sampler): `D_b` is the machine that the handler theorem
`Games.exists_handlerMachine` gives for `BB1Machine.handler … b q`, run on the adversary `A'` from
`Games.exists_toCompOn_of_toComp`.
- The handler is [BB04]'s algorithm `B` on encodings: group operations by `O : G.Ops`, residue arithmetic modulo
  `p = O.orderStr d` by `H : ArithmeticFP` (negation and differences as `(p − x) mod p`, `(x + (p − y)) mod p`, the inverse
  by `xgcdStr` with `0 ↦ 0`).
- With `n = κ + wG(κ) + 1`, the `j`-th exponent is `(sampleBelowL p (Nat.size p) n n w).getD 0` on the `j`-th block of `n²`
  coins (`BBM/Draws.lean`).
- `σ(κ) = (q(κ) + 1) · 2^{−κ}`. Four `ProbComp.abs_expect_sub_le` steps reduce to one tuple
  (`BB1Machine.abs_expect_bb1Sim_sub_distinguisherL_le`, the only new public lemma of `Oracles`); there, call by call,
  `bb1SimImpl` has the law of `drawStep` with fresh uniform exponents (the per-call identity through the **seven
  readers**), the tape lemma `expect_handlerMachine` turns `D_b`'s output into `A`'s guess, and `statClose_sampleBelowL`
  puts each draw within `(1/2)^n` of uniform since `0 < p ≤ 2^{wG} < 2^n`; the total is `q · (1/2)^n ≤ σ(κ)`.

**The seven readers** (Seyoon's ruling of 2026-11-16, minimal form, landing in this PR as pure insertions with `rfl` or
one-line proofs and formula docstrings; the 13-reader variant was not approved):
- `IB/Defs.lean`: `IBEScheme.oracleImpl_zero_onSpec`, `oracleImpl_one_onSpec`, `oracleImpl_two_onSpec` (each
  `(OracleComp.bind_pure _).symm`), inserted after base line 387;
- `IB/BonehBoyen.lean`: `ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK`, `bb1Scheme_msgSpace_iff` (after base line 387) and
  `ofFn_bb1SimCt` (after base line 551).

The approved text is `fills/bb1-machine/inhouse-r1/scope-request/BB1ReadersMin.lean.txt` (SHA-256 `8644e722…`, lines 27–68,
74–97, 99–109).

**LE-bb1m** (`89a18a82`, `Oracles.lean` only, +2/−8): removes an unused `have hpp` (BM-F01) and puts the docstring
arguments of `abs_expect_bb1Sim_sub_distinguisherL_le` in Lean order (BM-F02). No statement changes.

**Commits** (`checks/series.txt`; all seven SSH-signed, ed25519, verified with the public key in each signature, the same key
that signs the records tip; a one-byte tamper control fails):

| Commit | What | Files |
|---|---|---|
| `b4d9babc` | checkpoint 1 (in-house): drawn exponents; handler, Init round | `Draws`, `Handler` |
| `b9caa4ad` | checkpoint 2 (in-house): handler rounds and run; reduction lemmas | `Handler`, `Reduction` |
| `8abfa466` | checkpoint 3 (in-house): the handler's string layer split off; facade imports | `BonehBoyenMachine.lean` (+15/−0), `Draws`, `Handler`, `Words` |
| `61720b0e` | worker: the approved readers | `Defs` (+43), `BonehBoyen` (+37) |
| `43887330` | worker: the helper `Oracles` | `Oracles` (new) |
| `0da95f96` | worker: T4's body and sketch, the `Oracles` import, one `## Contents` bullet | `BonehBoyenMachine.lean` (+54/−17) |
| `89a18a82` | LE-bb1m (maintainer) | `Oracles` (+2/−8) |

The worker's three commits were delivered unsigned (exchange `f14ac810…`, `inbox/fills/bb1-machine/`); `git am` at the issue
base `7c0a55e0239c14786612d0cd4462e64238543ca1` reproduced their hashes (`633dcf99`, `b9a242ea`, `c90273fa`), and the landing
cherry-picks are `git range-diff` 6/6 identical (phase 2).

## Rulings and records in force

1. **Gate 40 is closed** (round 2 CLEAR, `findings/gate40-pairings-statements-r2-findings.md`, `e008f3a4…`). Its round-1
   findings (`ceb63bfc…`) judged T1–T4 true and gave the fill routes this gate checks against (§ *Truth and sufficiency
   of T1–T4*), including G40-03's sampler parameters for T4.
2. **Ruling G40-01** (injectivity fields `encPP_inj`, `encSK_inj`, `encCT_inj` on reachable objects; efficiency deferred,
   Q5). T4's per-call identity reads the scheme's encodings only through the four `BonehBoyen` readers.
3. **Ruling Q10** (pairing plan): T1 is attributed as folklore, "not stated in [BB04] or [Jou00]" (LE-gate40, G40-04).
4. **The T4 scope ruling** (Seyoon, 2026-11-16, decision-log row 413): the seven readers, minimal form, in the T4 PR, as with
   sc-yao's SY-3 readers; #331 unchanged; **Gate 44 checks that they are insertions only.**
5. **Rule 10 rulings:** `PolyExpr.eval` is notation (seal **A** canonical; seal B run and attributed); a `CoeFun`/`Coe`
   instance whose body is a projection is notation (**coe-A canonical**, the strict variant run and attributed); reducible
   abbreviations are notation; inside a file its own definitions may be read directly (`rfl`, `show`); each helper module
   is foreign to the others.
6. **The overnight authorization** (2026-11-16): the maintainer filled T1 in-house, to be audited by Codex.
7. **BS-F08** (decision-log row 427): Claude cloud sessions on this account share one commit-signing key, so a signature
   attests a Claude session on the account, not the maintainer; provenance rests on the pinned hashes.
8. **Not in scope:** the bb1-sim fill (T2/T3), its readers and its `Games/Relational.lean`; #351 and #352 (DW-11's combined
   gate).

## What is frozen

- **T1's statement**: its header (keyword to `:= by`) and its statement prose and `**Source:**` paragraph before
  `**Proof sketch.**`; every other declaration of `Pairing/Assumptions.lean` with its docstring, the module docstring, and
  every `variable`, `open`, `section`, option and comment. Permitted: the four imports after the base's last import, the
  two inserted blocks of private helpers, T1's sketch paragraph and body.
- **T4's statement**: header and statement prose; every other part of `IB/BonehBoyenMachine.lean`. Permitted: the
  checkpoint's four helper imports and `## Contents` section (pure insertions, `9e7a9648 → 7c0a55e0`, +15/−0), and then
  exactly the brief's regions (one `Oracles` import, one `## Contents` bullet, T4's sketch paragraph and body).
- **`IB/Defs.lean` and `IB/BonehBoyen.lean`** apart from the seven readers at their positions; **every other frozen file**
  (`BonehBoyenSecurity`, `Pairing/*` apart from T1's file, `KeyExchange/*`, `Games/*`, the facades).

## Questions for the audit

**1. True and sufficient targets, and correct proofs**
- **T1.** Does the body establish the frozen statement for every NUPPT solver `A`, under the stated order hypothesis
  `∃ δ, Negligible δ ∧ G.OrderAtLeastExcept (2^·) δ` and `h : G.DBDHAssumption`, with nothing else assumed? In particular:
  - Is `D` a non-uniform PPT in the library's sense, with `A`'s coins and advice (`exists_bdhDistinguisher`,
    `NUPPT.ofPolyTime`, `coinsCongr`), and polynomial-time on every input string, malformed ones included?
  - On `P_BDH`, is acceptance exactly `A`'s success? Is the coin move `coinsCongr`/`expect_sample_equiv` sound, and is the
    sample of `T` really unused?
  - On `R_BDH`, is the bound `Pr ≤ E_r[1/p]` right: the exchange of the two samples, injectivity of `encT` on the group the
    description `d` names, and `uprob_eq_one_div_card` for the target group's cardinality?
  - Is `1/p ≤ 2^{-κ} + [p < 2^κ]` correct for every `p`, `p = 0` or a degenerate group included, and is the bad-coin charge
    exactly `δ(κ)`? Is the final negligibility argument (`dbdhAssumption_iff`, `negligible_two_pow_neg`, `mono`) sound?
  - Does `accept_bdhGame_le` hold as stated for every `κ` (no "eventually" hidden in the hypotheses)?
- **T4.** Does the body establish the frozen statement for every `H`, `O`, `A`, `q`, both `b`, both tuple distributions and
  every `κ`, with `σ` chosen before `b`, `real`, `κ`?
  - Is `D_b` the [BB04] algorithm `B` on encodings, defined on every input string, malformed tuples and adversary answers
    included? Are the residue arithmetic modulo `p` (truncated subtraction avoided), the inverse with `0 ↦ 0`, and the
    membership tests sound?
  - Is G40-03's sampler used exactly (`n = κ + wG(κ) + 1`, `sampleBelowL p (Nat.size p) n n`, `getD 0`), and does
    `statClose_sampleBelowL`'s premise `p < 2^n` follow from `encG` injective (`0 < p ≤ 2^{wG}`) for **every** generator
    output, not only good ones?
  - Is the per-call identity `bb1SimImpl = castImpl (freshImpl drawStep)` exact for all three oracles, including refused
    and repeated key queries and invalid challenges? Is the tape argument (fresh exponents ≡ a tape drawn in advance;
    `expect_handlerMachine`; `abs_expect_runAccept_sub_le`) sound, with `q(κ)` exponents enough for every run?
  - Is `q · (1/2)^n ≤ (q + 1) · 2^{−κ}` right (`κ ≤ n`), and is `σ` negligible by the cited lemma?
- **Sufficiency.** At T44, `bb1_sidSecure` reaches `sorryAx` only through T2 and T3 (§ 8). Do T1 and T4 as proved leave the
  Gate 40 chain intact (T2–T4 suffice for `bb1_sidSecure`; T1 is not used by it)? Does anything in the T4 proof weaken
  what T2 must later supply?
- **Edge cases:** `κ = 0`; `q(κ) = 0`; `p = 1` or a generator output whose description is not a valid group; identity
  strings that collide modulo `p`; an adversary that never queries or never issues a valid challenge; `A` with zero coins
  or empty advice.

**2. Frozen-statement integrity** (`checks/headers.txt`, `checks/frozen-assumptions.txt`, `checks/frozen-t4.txt`,
`checks/readers.txt`, `replay/statements/touched-after.tsv`)
- **T1:** pair-bdh's `frozen_check.py`, rerun here from git objects (tip → T44): reverting exactly the four imports, the two
  private blocks, T1's sketch paragraph and body gives the tip's file byte for byte; the 10 inserted declarations are all
  `private`; T1's body has no `sorry`. Its six mutation controls (T1 header, another docstring, a public helper, T1 prose,
  a fifth import, another body) each FAIL, and the unmutated head PASSes. Do the permitted regions hold?
- **T4:** the review's `frozen_t4.py`, rerun (issue base `7c0a55e0` → `89a18a82`, blob-equal to T44): everything outside
  the four regions is byte-identical, and its ten controls each FAIL. The checkpoint's change `9e7a9648 → 7c0a55e0` is
  +15/−0 (the four helper imports and the `## Contents` section). T4's header and statement prose are byte-identical at
  `9e7a9648`, `7c0a55e0`, the tip, `89a18a82` and T44, and so are T1's at `9e7a9648`, the tip, `916afc25` and T44, and those
  of T2, T3 and `bb1_sidSecure` at the tip, `89a18a82` and T44. Do these checks show the statements unchanged?
- **Declarations** (`checks/decls2-tip-vs-T44.tsv`; `decls2.py` over the 9 files): 174 public declarations ADDED, 0
  CHANGED, 0 REMOVED. The declaration-level text comparison (`touched-after.tsv`) gives, over the 9 files, 99 UNCHANGED,
  2 CHANGED (exactly T1 and T4: docstring sketch and body), 17 ADDED to existing files (the seven readers and #340's ten
  private helpers) and 246 in the new files. Is any other declaration of a frozen file touched?

**3. The seven readers** (`checks/readers.txt`)
- The review's `readers_check.py`, rerun with base = the tip (whose `Defs`/`BonehBoyen` blobs equal `9e7a9648`'s and
  `7c0a55e0`'s): inserting the approved text (`8644e722…`) after `Defs:387`, `BonehBoyen:387` and `BonehBoyen:551`, each
  block after one blank line, gives the T44 files byte for byte (`4e220ead…`, `da875140…`); removing them restores the base
  (`9af4b773…`, `22caae4f…`); the diffs are +43/−0 and +37/−0. Its nine mutation controls each FAIL.
- Are these exactly the approved readers, verbatim, with `rfl`/one-line proofs and formula docstrings, no attribute? Is
  each needed under the seal (the reader control rows of #346's phase 2, below)? The `onSpec` statements contain
  `cast (show … from rfl)`: is that a definitional read of the file's own `sidSpec`, permitted inside `Defs.lean`, and not a
  hidden unfold for consumers?

**4. The landing edit LE-bb1m** (`89a18a82`): is it proof-only (an unused `have` removed) and doc-only (argument order), with
no statement change? Phase 2 found the request sets unchanged by it.

**5. Duplication** (recent gates graded undisclosed re-proofs of public lemmas as **majors**)
- **#340's 7 disclosures** (`fills/pair-bdh/inhouse-r1/REPORT.md` § *Overlap and reuse*): the machine as
  `NUPPT.ofPolyTime` of a raw function (the `NUPPT.wrap` alternative); `polyTimeComputable_pairEq` reused; the five-fold
  projection written out (there is `polyTimeComputable_iterate_pairFstD` but no iterated-`pairSndD` lemma);
  `prob_eq_encT_le` assembled from published lemmas (near alternative `ProbComp.expect_sample_mem_le`); the verdict identity
  `decide ([decide P] = [true]) = decide P` inline, although the public `decide_singleton_eq_true`
  (`Encryption/PublicKey/TrapdoorPredictor.lean`) states it (not imported, to keep the public-key layer out of the pairing
  closure); the order bound following ElGamal's private `dlc_uprob_bad_le`; the final inequality inline. Are these
  dispositions right? Is the inline verdict identity a re-proof of a public lemma that should be imported or ledgered?
- **#346** (review § *Duplication and reuse*, BM-F08/F09): `ofFn_padFin_ofFn` (a one-line specialization of
  `ofFn_padFin_of_length`), `cast_eq_padFin` (from `padFin_ofFn`, `cast_eq`), `ofFn_decAnswer_some` (`decAnswer_some` +
  `List.ofFn_cons`), the private `sidSpec_rng_one'`/`_two'` (promotion request, BM-F08), and the new public lemma
  `abs_expect_bb1Sim_sub_distinguisherL_le` (glue, BM-F09). The checkpoint helpers `Draws`, `Words`, `Handler` and
  `Reduction` (166 public declarations) were reviewed at the checkpoint (in-house REPORT). Is any part of the 174 new public
  declarations or of the proofs a duplicate of a public TCSlib or Mathlib lemma, or a copy of a private one, beyond these
  disclosures?
- Name clashes: none of the 9 files' declarations (private included) has an exact full-name clash anywhere else in
  TCSlib at T44 (`checks/nameclash-T44.txt`); #340 adds no public name.

**6. Rule 10** (`rule10/`; § 9 has the figures)
- **Seals on the changed owners whose request sets change in T44.** `Pairing/Assumptions` (#340's owner) and #346's five
  owners downstream of it (`BBM/Words`, `BBM/Handler`, `BBM/Reduction`, `BBM/Oracles`, `IB/BonehBoyenMachine`): strict and
  coe, A and B, 24 seals. Are they canonical, closure-complete and bound to T44?
- **The other three #346 owners** (`IB/Defs`, `IB/BonehBoyen`, `BBM/Draws`) do not import `Assumptions`. They were not
  re-sealed: a collector run over all eight #346 owners at T44 gives request sets **row-identical** to phase 2's snapshot-#4
  records (`2ec72515`), whose seals passed. Is request-set identity (with the owner sources and probes byte-identical) a
  sufficient ground?
- **The unchanged Gate 40 owners downstream of the changed files** (`KeyExchange/Joux`, `IB/BonehBoyenSecurity` and the
  facades `AdvancedEncryption/IdentityBased` and `AdvancedEncryption`) were **re-sealed** on T44 (the supplement, by the
  coordinator's ruling): their request sets grew since Gate 40's merged-tree seals, so identity could not be shown. Strict and
  coe, A and B, with Gate 40's paired controls (`supplement/`, § 9). `Pairing/Group` and `Pairing/Operations` are not
  downstream of the changed files. Are these seals canonical and bound to T44?
- **Paired controls on `Assumptions`** (pair-bdh's `mkctl_pbdh.py`: LE-gate40's rows plus nine rows for `distinguisherL`,
  `runAtL`, `layout`, `ofPolyTime`, `advInput`, `accept`, `uprob`, `OrderAtLeastExcept`, `inst`), strict and coe.
- **The explicit-unfold scan** over the 9 changed files. Does any proof read a foreign definition other than through a
  published reader, in particular `encT`, `pairEncode`/`pairFstD`/`pairSndD`, `NUPPT` layouts, `sampleBelowL`, `inLens`,
  `outLens`, `sidSpec`, `oracleImpl`, `bb1SimImpl`, `freshImpl`, `castImpl`, the encodings and `Ops`?

**7. Sources and citations** (`checks/sources.txt`; `sources-r1.zip` `references/`)
- **T1's attribution:** "not stated in [BB04] or [Jou00], which define the two problems ([BB04, §3.1]). The implication is
  independently derived here: the folklore fact that deciding is no harder than computing." Is that accurate against the
  BB04 and Jou00 transcriptions, and is "folklore" an acceptable attribution under ruling Q10?
- **T4 and the helpers:** [BB04, §4.2, the algorithm `B` in the proof of Theorem 4.1, whose cost is the theorem's
  `Θ(τ ℓ q_S)`]; the helpers' `[BB04, proof of Theorem 4.1]`; the module docstring's "[BB04, pp. 7–8]" against the
  References entry "§4.2 (pp. 6–8)". Are the locators right?
- **`BBM/Draws.lean`'s `draw`** cites **[PS10, Theorem 52.3]** for "an exponent of `Z_p` drawn from `n · n` coins" by the
  rejection sampler `sampleBelowL`. `references/pass-shelat-2010-ch2.raw.lines1338-1420.md` has §2.8 with Theorem 52.3
  (the discrete-log collection; its proof says "It is easy to sample the domain `D_i`"). Is this an apt citation, or a
  stretched locator that should name the library's sampler source instead?
- New tags at T44 appear only in the five new helper files (`[BB04]`, `[BB04, proof of Theorem 4.1]`, `[PS10]`,
  `[PS10, Theorem 52.3]`); the four modified files gain no tag. Every key used has a `## References` entry except
  `Assumptions.lean`'s `[Jou00, SOK00, BF01]` (BB04 §3.1's credit line; `SOK00` and `BF01` have no entry), which is at the
  tip already (#331, Gate 40 closed). Is any tag fabricated or wrong?

**8. Docstrings and sketches**
- Every new public declaration has a docstring that states its formula in Lean argument order (BM-F02 fixed by LE-bb1m).
- Every proof of 15 lines or more carries a `**Proof sketch.**` (`lint/sk15-9files.txt`: the only hit is
  `BonehBoyen.lean:631 bb1SimChal_fresh`, pre-existing from #331, BM-F06, outside both PRs).
- Do T1's and T4's sketches describe the delivered proofs? Note that T4's sketch and `Oracles`' module docstring call
  `Games.exists_handlerMachine` "the handler theorem T1", the Games campaign's own label, which is not this campaign's T1
  (`bdhAssumption_of_dbdhAssumption`). Is that confusing enough to fix?

**9. The joint replay and the axioms** (the merge-condition evidence; `replay/`)
- Does the replay bind to T44, and does it show no regression? Is anything necessary missing (a missing necessary piece of
  evidence is a **major**)?

**10. Is anything undisclosed?** Among the two PRs' commits, their descriptions, the two maintainer reviews and the records
after them, is any change, claim or omission undisclosed? The known slips are listed below.

## The joint replay on snapshot #4 (maintainer, 2026-11-17)

Recipe: `briefs/pass-shelat-ch5-8/maintainer/snapshots.md` (job recipe) and `workflow.md` on `main` §6.1. Tools: the
snapshot recipe's (`olean-rebase-dl-oleans-2/…/tools-used/`, as copied into #346's phase-2 `tools-used/`) unmodified; the
seal harness is phase 2's `tools-used/seal` unmodified, plus pair-bdh's `mkctl_pbdh.py` unmodified; the drivers are new
(`replay/tools/run-build-g44.sh`, `replay/tools/rule10_g44.sh`). One Lean process at a time.

- **Copy and overlay.** Snapshot #4 rehashed 0 extra / 0 changed / 0 missing against its map before the copy. `cp -al` gave
  `$SP/olean-replay-g44` (1453 files, all hard links). The Mathlib overlay (3346 symlinks) and NthRootLemmas
  (`c0a9cff0…`) were added to the output only.
- **Plan.** `stateplan.py init` at `463f2244` keys 1422 modules; `downorder.py` gives 9 changed and 16 downstream;
  `fullorder.py` gives the closure of root `TCSlib` and both `audits/*/Checks`, 1427 modules (closure check: 0 missing,
  0 extra). The plan builds **16** and reuses 1411; the queue equals the downstream set: `Pairing/Assumptions`, `Pairing`,
  `KeyExchange/Joux`, `KeyExchange`, `IB/Defs`, `IB/BonehBoyen`, the five helpers, `IB/BonehBoyenMachine`,
  `IB/BonehBoyenSecurity`, the facades `IdentityBased` and `AdvancedEncryption`, and root `TCSlib`.
- **Build** (`runner.py` through `scripts/lean_check_tree.sh`, 03:52–03:53 UTC): **16/16 rc 0, 0 `error:`, 0 `error(`, 0
  occurrences of "error"**. Warnings: exactly 2, both `declaration uses 'sorry'` in `BonehBoyenSecurity` (T2, T3); the 9
  changed modules have 0. All 16 oleans are byte-identical to earlier committed builds of the same sources
  (`replay/checks/olean-vs-refs.txt`): `Assumptions` to int-x-341-340's B and phase 2's cross-build X; the #346 modules to
  346c's.
- **State.** `stateplan update` took 16; `stateplan check` over the 1427-module full closure: **RESULT OK**.
- **No write-through.** All 16 rebuilt oleans have link count 1; no `.ilean`. Snapshot #4 rehashed **0/0/0** after the
  replay and again at the end of the job.
- **Output** `$SP/olean-replay-g44` is **kept**: it becomes snapshot #5 if #340 and #346 both merge and the final merge
  commit's Lean equals T44. Its map without `Mathlib/` (what `snapmap.py make` gives after recipe step 6) has 1458 entries,
  SHA-256 `ded2f64d177fc73a55c8f55e0ad1bc4699392c2a53c7cfb45f9152b55ed4abda`; against snapshot #4: 1449 equal, 4 changed
  (`Assumptions`, `Defs`, `BonehBoyen`, `BonehBoyenMachine`), 5 added (the helpers).
- **Admissions** (`tipcensus.py`, build records of every snapshot generation plus this job's; `replay/admissions/`): tip
  `1d1a9bb3` **198**, T44 **196**: **−2, exactly `Pairing/Assumptions` (T1) and `IB/BonehBoyenMachine` (T4)**; the five
  helpers have 0. No record disagrees; the same 34 modules outside root `TCSlib`'s closure have no record.
- **Axioms** (`replay/probe-src/Axioms44.lean` = phase 2's `Axioms346.lean` plus `Pairing.Assumptions` in the census; rc 0,
  0 errors):
  - **T1** `bdhAssumption_of_dbdhAssumption` and **T4** `exists_bb1_distinguisher`: `[propext, Classical.choice,
    Quot.sound]`; dependency trace: T1's closure 17314 constants and T4's 19638, each reaching **0** sorried constants.
  - The public lemma, the four `BonehBoyen` readers and three `BB1Machine` helpers: the standard three; the three `onSpec`
    readers: `[propext, Quot.sound]`.
  - **`bb1_sidSecure`**: `[propext, sorryAx, Classical.choice, Quot.sound]`, and its closure (19674) reaches **exactly
    `bb1_sim_real` and `bb1_sim_random`** (T2, T3).
  - Census of the 9 owners: **604 constants, 0 non-standard.** The summary differs from 346c's only in T1's row (now
    standard).
- **Rule 10.** Every probe ran through phase 2's `runner_full.py` (`lean -DmaxErrors=0`, no `-o`), on `$SP/olean-replay-g44`;
  both error forms are counted from the raw logs (`rule10/*/error-forms-*.txt`).
  - **`Pairing/Assumptions`** (collector over that owner alone, then `rule10_b.sh` unmodified): strict A/B and coe A/B,
    requests **895 / 896 / 894 / 895**, each rc 0, 0 `error:`, 0 `error(`, install and EOF records, no failing declaration.
    The four request sets are **row-identical** to pair-bdh's in-house seals at `916afc25` (and coe A/B to phase 2's
    cross-build X), and the four probe sources are byte-identical (`rule10/compare/assumptions.txt`).
  - **Paired controls on `Assumptions`** (`mkctl_pbdh.py`): 4 sealed and 4 unsealed probes per variant; the 25 sealed
    negatives per variant (12 in A, 13 in B, which also has `PolyExpr.eval`) each fail exactly once (50 `error:` lines in
    each of strict and coe, 0 `error(`), every reader passes, every unsealed probe has 0 errors: **ALL_OK True** in strict
    and in coe. Both `ctlcheck` results are identical to pair-bdh's.
  - **The five #346 owners downstream of `Assumptions`** (collector over all eight #346 owners): strict A/B and coe A/B,
    **20/20 rc 0, 0 `error:`, 0 `error(`**, install and EOF records, no failing declaration. Requests (strict A / strict B /
    coe A / coe B): `Words` 2243/2244/2242/2243, `Handler` 2276/2277/2275/2276, `Reduction` 2310/2311/2309/2310, `Oracles`
    2311/2312/2310/2311, `BonehBoyenMachine` 2312/2313/2311/2312. Each is phase 2's snapshot-#4 count **+2**, and the added
    rows are exactly #340's private `Pairing.tupleBdh` and `Pairing.tupleTgt`; 0 rows removed. The 20 request sets are
    row-identical, and the probes byte-identical, to phase 2's cross-build X seals (`b90b966b`), which also passed.
  - **Not re-sealed, by request-set identity:** `IB/Defs` (805/806/804/805), `IB/BonehBoyen` (840/841/839/840) and
    `BBM/Draws` (1645/1646/1644/1645). Their records at T44, from the same collector run, are row-identical to phase 2's
    snapshot-#4 records (`2ec72515`), with owner sources and probe sources byte-identical; phase 2 sealed them (32/32,
    0 errors) and reconfirmed coe A on snapshot #4 (`rule10/compare/owners.txt`).
  - **Explicit-unfold scan** over the 9 changed files: 1016 items (750 THEOREM, 166 LOCAL_OR_UNRESOLVED, 98
    OWNED_DEFINITION, 2 SIMPROC), **0 foreign**; it is exactly the union of pair-bdh's 69 items and 346c's 947. The kinds
    probe had rc 0.
  - **Supplement: the unchanged Gate 40 owners downstream of the changed files** (`supplement/README.md`; run 04:35–05:01
    UTC; collector over the four, then `rule10_b.sh` unmodified with LE-gate40's `mkctl_g40.py`): `KeyExchange/Joux`
    904/905/903/904, `IB/BonehBoyenSecurity` 2312/2313/2311/2312, `AdvancedEncryption/IdentityBased` 2312/2313/2311/2312,
    `AdvancedEncryption` 2409/2410/2408/2409 (strict A / strict B / coe A / coe B). **16/16 rc 0, 0 `error:`, 0 `error(`**,
    install and EOF records, no failing declaration. Against Gate 40's merged-tree seals (`9e7a9648`) every record gains rows
    (Joux +253, `BonehBoyenSecurity` and the `IdentityBased` facade +1208, the `AdvancedEncryption` facade +1161) and loses
    none, with the owner sources byte-identical. Paired controls (covering subset: the `IdentityBased` facade and `Joux`):
    24 sealed negatives per variant each fail exactly once, every reader passes, every unsealed probe has 0 errors: **ALL_OK
    True** in strict and in coe. `BonehBoyenSecurity` declares no definition; its request sets equal the facade's row for
    row. Snapshot #4 rehashed 0/0/0 before and after; the output still matches its map `ded2f64d…`.
  - **Name clash** (`checks/nameclash-T44.txt`, phase 1's `nameclash.py` over every declaration of the 9 files, private
    included, against every other TCSlib file at T44): **0 exact full-name clashes**.
- **Lint** (`campaign_style_lint.py TCSlib/Cryptography --check8b`, tip and T44 exports): 92 FAIL / 104 WARN on both sides,
  the non-INFO line sets identical (only the file count of the summary line changes, 519 → 524), so **no new FAIL or
  WARN**. The INFO changes are the size and declaration-count lines of the 9 files (`BonehBoyen` 714, `Handler` 899 and
  `Words` 632 over the 600 target, all under the 1000 cap). `style_lint.py` on the 9 files: 0 findings.

## Known dispositions and slips (not findings)

- **#346's review findings** (`fills/bb1-machine/final-r1/review.md`): BM-F01 (info) and BM-F02 (minor) fixed by LE-bb1m;
  BM-F03 closed by phase 2's `Oracles`-owned controls (ALL_OK); BM-F04 superseded; BM-F05 evidence nits; BM-F06
  (`bb1SimChal_fresh`'s 15-line proof without a sketch, pre-existing, cleanup ledger); BM-F07 sizes; BM-F08 (promotion
  request for `sidSpec_rng_one/_two`, carried to the bb1-sim reader probe); BM-F09 (the public glue lemma). Grade them.
- **#340's in-house "Not yet done"** (REPORT § *Limits*): the downstream owners' seals after `Assumptions`' closure grew.
  Phase 2's cross-build X sealed the five #346 owners downstream of `Assumptions` (20/20, 0 errors, each request set +2
  rows: `tupleBdh`, `tupleTgt`), and this gate's replay seals them on T44.
- **The PR descriptions** were updated by Seyoon on 2026-11-17 (#340 at 04:34:27Z, retitled "Pairing fill pair-bdh: T1
  bdhAssumption_of_dbdhAssumption", base, joint check and seal status corrected; #346 at 04:34:39Z, with phase 2 and the
  joint check). `pr340-description.md` and `pr346-description.md` are those bodies, read with the GitHub MCP tool and the
  REST API (the same text). The REST `base.sha` fields (`b6d977ea…`, `7291f6b2…`) are the tips at retarget and at opening;
  records commits only have landed since.
- **Authorship.** T1 and #346's three checkpoints were written in-house by the maintainer; #346's middle three commits by an
  external Claude worker; LE-bb1m by the maintainer. The signing key is shared by the account's Claude sessions (BS-F08).
- **The 346c replay** (#346 alone on snapshot #4, `$SP/olean-replay-346c`, map `5e63b3cc1a0efd40c3b5875d701b99a7457cc5f2a3b2831d4a7ab8cc7cf35404`,
  rechecked equal at staging) is kept as well, in case #346 merges without #340.
- **Phase 2's seal evidence on snapshot #2** (32 seals, 314 sealed negatives per variant, the `Oracles` controls) is in
  `fills/bb1-machine/final-r1/phase2/phase2-evidence.zip`; it is not copied here (28 MB). A pointer and the cited summaries
  are.

## Merge interaction (maintainer merge conditions, not audit items)

- Merge both PRs together, or #346 first: the replay output `$SP/olean-replay-g44` is adoptable as snapshot #5 only if the
  final merge commit's Lean equals T44 (procedure step 3). If #346 merges alone, `$SP/olean-replay-346c` is adoptable
  instead, and #340 then re-replays.
- #340's base is `cryptography/pass-shelat-ch2-4` (checked with the GitHub tools at staging); it is not stale.

## Evidence files

- **`pack-r1.md`** (this file), **`dispatch-r1.md`** (the Codex prompt; records only).
- **`pr340.diff.txt`** (`git diff 9e7a9648..916afc25`, equal to the three-dot `git diff 1d1a9bb3...916afc25` byte for byte;
  1 file, +227/−8), **`pr346.diff.txt`** (`git diff 7291f6b2..89a18a82`, equal to the three-dot view; 8 files, +2741/−17),
  **`T44.diff.txt`** (`git diff 1d1a9bb3 33681cb8` over the code paths; the 9 files).
- **`pr340-description.md`**, **`pr346-description.md`**: the PR bodies as updated on 2026-11-17 (REST `.body`, raw).
- **`source-head-r1.json`**: the pins and, for each of the 9 files at T44, status, SHA-256, line count and over-width count.
- **`sources-r1.zip`**: `T44-33681cb8/` the source closure at T44 (168 modules: the import closure of the `IdentityBased`,
  `KeyExchange` and `Pairing` facades); `pr340-head-916afc25/` and `pr346-head-89a18a82/` the changed files at each head;
  `tip-1d1a9bb3/` the four changed files at the tip; `references/` the BB04 and Jou00 transcriptions (DW-7), Gate 40's
  excerpts, and the [PS10] §2.8 lines with Theorem 52.3. Its `README.md` gives every entry's SHA-256 and origin.
- **`verification-r1.zip`**: `MANIFEST.md` (the layout and each entry's provenance) and `SHA256SUMS` (every other entry).
  - `replay/`: the joint replay (landing trees, export and copy, orders, state, plan, the build with every module log,
    the Mathlib extra, link counts and base rehashes, the olean comparison, the output map, admissions, axioms with the
    probe source and log, statements, lint) and its drivers and tools;
  - `rule10/`: the `Assumptions` seals and controls, the five owners' seals, the records of the three owners not re-sealed
    (`own/rel/`), the request-set comparisons (`compare/`), the scan, with probe sources, run records and logs;
  - `checks/`: the re-checks from git objects (series and signatures, merge trees, headers, the T1 frozen check, the
    reader-insertion check, the T4 frozen check, decls2, sources, the reviews' evidence integrity), with their scripts;
  - `reviews/`: the two maintainer reviews (#346: `review.md`, phase 2 `README.md`, both `SHA256SUMS`; #340: the in-house
    `REPORT.md` and the int-x-341-340 `README.md` and `SHA256SUMS`), and `POINTERS.md` with the path, size and SHA-256 of
    every review evidence ZIP at the records tip (not copied);
  - `records/`: the pairing plan and its decision-log extract (rows of 2026-11-16 and 2026-11-17 from Gate 40's findings
    to #346's phase 2), Gate 40's round-1 and round-2 findings and round-2 resolutions, the approved reader text, #346's
    issue brief, and `policy.md`;
  - `pr/pr-rest-fields.json`: the REST fields read after the description updates;
  - `supplement/`: the seals and controls of the unchanged Gate 40 owners downstream of the changed files (§ 9).
- **`SHA256SUMS-r1`**: the files of this gate directory.

## Findings delivery

Return `gate44-pairing-fills-findings.md` as Markdown in this chat. If you have several evidence files, return a ZIP. The
user dispatches and merges.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Grade BM-F01 to BM-F09 and #340's seven overlap disclosures in a separate table (agree, or regrade with the reason). Report
the audited heads, T44 and the counts by severity. The gate closes at zero blockers and zero majors.

**Severities**
- **blocker:** a false or unusable statement, a proof that does not establish the frozen statement, or a scope violation.
- **major:** any of the following:
  - a changed frozen statement;
  - a reader beyond the approved seven, or a reader that is not a pure verbatim insertion;
  - a forbidden read in a touched declaration not covered by the rulings;
  - an undisclosed copied private lemma, or an undisclosed re-proof of a public one;
  - a fabricated source tag;
  - necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, proof sketch or citation.
- **note:** anything else.
