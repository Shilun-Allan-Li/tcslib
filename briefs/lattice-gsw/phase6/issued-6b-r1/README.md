# Claude statement job `gsw-6b-statements` (GSW phase 6b statements, and owner PR O2)

Claude is the worker, a lead with up to 3 sub-agents (the 6a precedent: statement jobs go to an external Claude session
that Seyoon dispatches; Seyoon's 6b staging ruling of 2026-11-17, `LatticeCryptographyPlan.md`, decision log). The job
writes the statement phase of phase 6b from plan section r3 (`../plan-section.md`, §H7 items 4–5): the statements of
units U12–U19 in eight new files under `Cryptography/AdvancedEncryption/Homomorphic/GSW/` and `Cryptography/LWE/Ratio.lean`
(homomorphic PBP evaluation, the decryption formula, NAND bootstrapping, weak circular security, the leveled scheme
and its key hybrid, the polynomial ratio, the asymptotic forms), the two facades, and owner PR O2
(`decode_iff_mem_Ico` in `LWE/BitEncoding.lean`, proved; it does not exist at the base) as a separate series. Gate 46
(Codex) audits the delivery.

| Unit | New file | Rows | Admitted targets |
|---|---|---|---|
| O2 | `LWE/BitEncoding.lean` (existing) | G4 → `decode_iff_mem_Ico` | 0 (proved) |
| U12 | `GSW/Branching.lean` | G1–G3 | 3 |
| U13 | `GSW/DecryptFormula.lean` | G5–G8 | 6 |
| U14 | `GSW/Bootstrap.lean` | G9–G13, G18 | 5, + G11 as a citation |
| U15 | `GSW/Circular.lean` | G14–G15 | 1 (G14 reader-only, Q-6B-1) |
| U16 | `GSW/Leveled.lean` | L1–L3 | 2, + L1 as a citation |
| U17 | `GSW/LeveledSecurity.lean` | L4–L5 | 2 |
| U18 | `LWE/Ratio.lean`, `GSW/PolyRatio.lean` | G16–G17 | 2 (3 if G17 is split) |
| U19 | `GSW/Asymptotic.lean` | A1–A3 | 2 (A2 reader-only, Q-6B-1) |

25 r3 rows: 23 admitted targets (24 if G17 is split), 2 citations (proved now if one step from a phase-5 lemma, else
admitted), 2 reader-only rows. `targets.txt` has the row map and the counts.

**Base** `3e51b5f28900db6190f1eb2e6d207d27ee15d541` (tree `b69a66a385ca3439d56af1d6b9791b5847984fde`), a deterministic
unsigned two-step merge: #360's head `cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25` into #359's head
`d154c8830fc8ffc52671b41992e7dbef61e30959` (step 1 `04947bcf35e08ed5f3a4902b2637a77482fd32d2`), then step 1 into the
records tip `036d823933c8248bd8894c7963e15dd0f1837075` (Lean = snapshot #6, #357's merge `8060f6b7`).
- Both merges are clean. The base's Lean is the tip's plus exactly the 23 Lean files of #358, #359 and #360.
- `tools/mkbase.sh` and the brief's `git merge --no-ff` recipe both re-create it and check every hash; the maintainer
  ran both and got `3e51b5f2…` both times.
- **#358, #359 and #360 are unmerged drafts**. Gate 45 round 2 closed CLEAR on 2026-11-17 at exactly these heads, with
  no statement change (records `5ac18f4e`), so the 6a statements are frozen. The 97 6a targets are admitted at the base
  (their proofs are being landed separately on `land/gsw-6a-fills`), and the 6b statements cite them as frozen
  statements. If a 6a statement still changed before landing, the maintainer would re-pin this job.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md) (v1, Part 1 unchanged, with an
adaptation for this job: the cloud Lean pool of `workflow.md` §4.1 and a root build). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

**Pack contents** (made from git objects of the base by the packaged tools; nothing was checked out or built):
- [Build order](order.txt): the **1,443** modules reachable from `TCSlib.lean` at the base, in import order (a
  depth-first post-order, imports in file order), root last: the root build. 34 files under `TCSlib/` are not reachable.
- [Prefix](prefix.txt): the **288** modules of the order the job needs first, the upstream closure of the `DOWN` and
  `IMPORTS` modules of [closures.txt](closures.txt). `CHANGED` holds the 3 existing files the job edits
  (`LWE/BitEncoding`, the facades `LWE` and `GSW`); `DOWN` holds the 18 modules downstream of them (root excluded), the
  sweep; `IMPORTS` holds the 22 existing modules the r3 sketches cite. Neither `audits/*/Checks` is downstream of a
  changed module.
- [Mathlib roots](roots.txt): 385 for the order; [prefix roots](prefix-roots.txt): 105 for the prefix.
- [Source hashes](SOURCE-SHA256SUMS) of the 1,443 files at the base.
- [Base admissions](base-sorries.txt): **289 declarations in 55 modules**, from a syntactic scan (comments and strings
  stripped, `sorry` tokens attributed to the enclosing declaration); 97 of them are the 6a targets in 11 modules. The
  final must add exactly the delivered 6b targets (23 to 26) in the 8 new GSW files.
- [Targets](targets.txt): the 25 r3 rows with unit, file, r3 name, kind and source.
- [Pins](pins.txt): where each of 106 TCSlib names the r3 6b sections cite is declared at the base (r3's own line
  numbers are at the 6a issue base `f6f295a6`, before the phase-5 fills merged). [Census](census.txt): a static reader
  census of 64 foreign definitions the 6b sketches read; one MISSING reader, `hybridPlant`.
- `tools/`: `mkbase.sh` (the base); `graph.py` (the fills pack's, unchanged except two docstring lines) and
  `plan6b.py` (order, prefix, roots, closures, admissions), with their inputs `changed.txt`, `imports.txt`,
  `closures.header`; `pins6b.py` with `pin-names.txt` (and `r3-names.txt`, the staging name check); `census.py` with
  `census-list.txt`; `o2check.py` (O2's interval form against `decode`, 0 mismatches for every residue of every
  modulus `2 ≤ q ≤ 2000`).
- The exchange pack adds `inputs/` (with its own `SHA256SUMS`): plan section r3, `rulings.md`, Gate 45's round-1
  findings and resolutions and round-2 findings, the 6a statement delivery's final and checkpoint reviews, and the 6a
  fills' phase-1 review, byte-identical to the records (SHA-256 in the brief, *Inputs*).

**Maintainer's checks at staging** (no Lean run):
- Both merge forms reproduce the base; `lean-toolchain`, `lake-manifest.json` and the lakefile are blob-identical at the
  base, the three heads and the records tip.
- `decode_iff_mem_Ico`, `decodeLo` and `decodeHi` exist on no branch, so O2 is needed; `o2check.py` passes.
- Every TCSlib name the r3 6b sections cite exists at the base (`pins.txt`: 106 found, 0 not found).
- None of the 65 definition and target names of r3's 6b sections (`tools/r3-names.txt`, run through `pins6b.py`) is
  declared at the base (`WeakCircularSecure`, `RatioBounded`, `ofFamily`, `bootNoise`, `keyBits`, `homEvalPBP`,
  `encodeView`, `ReductionEfficient`, …), except the short name `select` in two unrelated files
  (`Complexity/TuringMachine/Build/Embed.lean:1092`, `Cryptography/Randomness/Extraction/Rejection.lean:185`); the open
  PR #355 adds none of them.
- Lint at the base: `style_lint` 0 findings in the three changed files; `campaign_style_lint TCSlib/Cryptography
  --check8b` 92 FAIL / 104 WARN over 529 files.
- r3's G14 and A2 restate their predicates' own `_iff` readers (G45-01): staging question **Q-6B-1** (the brief applies
  the recommended option A, reader-only, which leaves the admissions unchanged). r3's G15 restates phase-5
  `distAdv_encrypt_le` unless it is stated over the projection of `fheView`; the brief says so.

Claude returns at least one checkpoint and the final only at `inbox/fills/gsw-6b-statements/` on the exchange; each
checkpoint carries the head hashes, the patches to them and `src/` of every file it claims compiles (lesson
G6A-C1-F01). It never pushes a campaign branch. Seyoon dispatches with the prompt in the records' `dispatch.md`
(beside this file in `briefs/lattice-gsw/phase6/issued-6b-r1/`; it is not part of the pack).

**Size** (maintainer's assessment). About 1,300–1,800 statement lines in 9 new files, O2 (60–90 proved lines), two
facades, and the full evidence of a statement phase, including a 1,452-module root build through the pool. One job is
right; the files depend on each other's definitions, so the suggested split has the lead write O2 and the bootstrapping
core (checkpoint 1) before sub-agents `lev` (leveled scheme) and `asy` (ratio, asymptotics) start, with `probe` on the
probes and scans. If the job must be split, split it at checkpoint 1: 6b-1 (O2, U12–U15) and 6b-2 (U16–U19, stacked
on 6b-1's head).

**Maintainer steps before dispatch:** commit this folder to the records branch (the exchange pack equals it, plus
`inputs/`), write that commit's full hash as the records pin in `dispatch.md`, and push the exchange commit named
there. If it is replayed onto a newer exchange tip, its hash changes: put the pushed hash in `dispatch.md`.

**Ready to dispatch**
