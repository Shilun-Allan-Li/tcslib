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
