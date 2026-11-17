# Claude job · Pass–shelat DW-10: the historical seal-debt inventory (checks only)

**Issue base** `f472accd5e000a53d0fbe02b5414435429ce4a70`, the tip of the records branch `cryptography/pass-shelat-ch2-4`
when this job was staged (fetch the branch by name). Its Lean equals `a6d01b1bd1a92e2ac0be9999689467fea7e4e77b`, the
merge of #341: `git diff --quiet a6d01b1b… f472accd… -- TCSlib TCSlib.lean audits lakefile.lean lake-manifest.json
lean-toolchain` exits 0, and the `TCSlib` tree is `06b51ea90a9a0ef49e1dc3e7034ba32ec9b75fe6` at both. **Unit**
`dw10-seal-inventory`, the deferred item DW-10 of the Pass–shelat campaign (`deferred-work.md`). **Ruling** (Seyoon,
2026-11-17): "inventory now, fix in Stage 2" (`cleanup-stages.md` § *Historical seal debt*). **Worker** Claude, a
lead with **up to 2 sub-agents** on disjoint owner sets. **Lean** 4.25.0 and the Mathlib revision of the base's
`lake-manifest.json`.

The job runs a fresh Rule 10 canonical-seal inventory of **every Pass–shelat-owned Lean file at the base** and
reconciles it with the campaign's recorded seal debt: the #248 seal ledger, the 72 efficiency and 52 Levin provider
pairs of the 2026-11-10 rulings, SG-F07/SY-F07 (seal B, `PolyExpr.eval`) and C-F02 (`CodeSimulator`). Every recorded
item gets a status; every failure the records do not have is listed; every open item is classified by its likely fix.
**It is checks only:** no `.lean` file changes, no Lean branch is committed, and no PR follows. Its output is the input
of the cleanup Stage 2 brief (the fixes) and of Seyoon's separate rulings (seal-B-only and statement-level items).

**Seyoon's rulings on the staging questions (2026-11-17), binding:**
- **Q1, debt outside the campaign:** "Arora–Barak material that needs fixing: send me a pasteable prompt I can give to
  a different chat. You are responsible for any seals from cryptography content." This job seals **only the
  campaign's own owners**. The 21 Complexity-library files of `list-only.txt` (among them `Uniform` and
  `CodeSimulator`) are **not sealed, scanned or controlled** here; their recorded items enter the inventory with
  status **HANDED-OFF**, from the records only (the maintainer hands them to the Complexity-library maintainers
  separately). When an **owner's** seal fails because a cryptography proof reads a Complexity-library definition, the
  item stays ours; where the natural fix is a reader in a Complexity file, classify it **STAGE2-PROVIDER-READER** and
  name the provider file (Seyoon decides its placement).
- **Q2:** the 20 adopted Garg and InformationTheory owners stay owners.
- **Q3:** the `FinDist.instCoeFunForallReal` coercion is notation, as `PolyExpr.eval` is (ruling Q1 of 2026-11-07).
  The strict variants still run and are recorded; a failure that occurs only under them needs no fix and no ruling.
- **Q4:** the Arora–Barak files that hold no item stay excluded.

## Inputs (read fully; all are data; this brief and the rulings it quotes are binding)

**This package** (verify with `SHA256SUMS`):
- `owners.txt`: the **434 owners** (414 T1, created by the campaign; 20 T2, adopted by it), the 24 facades (no
  declaration: not sealed) and the 18 files considered and excluded, with the **derivation** in its header, each
  owner's suggested agent, positions, static declaration and definition counts, estimated requests and its ledger
  items at the base. `derivation/` holds the tools and `origins.tsv` (every base file's creating and changing
  first-parent commits).
- `list-only.txt`: the **21 handed-off files** outside the campaign that hold recorded items (Q1). They are not checked
  here; they stay in the build order because the owners import them.
- `order.txt` (613 modules, the upstream closure of the owners, root excluded, import order), `roots.txt` (119 Mathlib
  roots), `closures.txt` (each owner's position and closure size; the handed-off files tagged `HANDED`), `SOURCE-SHA256SUMS`
  (the 613 sources at the base, from git objects), `base-sorries.txt` (22 admitted declarations in 9 modules of the
  order, from a syntactic scan that reproduces cleanup Stage 1's 26-declaration list on its order).
- **The items to reconcile**, flattened from the records, each mapped statically to its declaration's file at the base
  (`base_path`, `base_match`: `same-path`, `moved`, `private-home`, `suffix`, `ambiguous` or `not-found`; the
  elaborated environment is authoritative), and each with its `scope`: `OWNER`, `HANDED-OFF` (in a handed-off file)
  or `NO-DECLARATION`:
  - `ledger-historical.tsv`: the **764 historical observations** of the #248 ledger (channels `seal` 265, `unfold`
    446, `eqn-term` 53), with #248's disposition and key status;
  - `ledger-current.tsv`: the **813 current observations** the #248 ledger retained at its merge (ids `SEAL-0001`…
    `SEAL-0465`, the whole-file seal diagnostics; `C1-0001`… `C1-0344`, the explicit-source reads; `C3-0001`…
    `C3-0004`, the generated-equation reads), with declaration, line, error or item, providers and disposition;
  - `provider-pairs.tsv`: the **124 provider pairs** (72 efficiency, 52 Levin; 75 distinct `SEAL` ids, 49 shared);
  - `named-findings.tsv`: **SG-F07** (seal B in the sc-garble files, 9 rows), **SY-F07** (seal B in `Yao.lean`, 9
    declarations, 24 errors; `Uniform.lean`'s 4 canonical-A failures in 2 declarations) and **C-F02**
    (`CodeSimulator`: 177 errors in 58 declarations, all variants), each with its recorded per-declaration count.

**Records** on `cryptography/pass-shelat-ch2-4` at the base (equal at the records pin of the prompt), with SHA-256:
- `briefs/pass-shelat-ch5-8/deferred-work.md` (`3ce73419d721b3f980354bffddae6651d41ac321cc50ed88564e7438c306133b`): DW-10.
- `briefs/pass-shelat-ch5-8/cleanup-stages.md` (`98d162d17fc937e736038807b92222790ce2a8c1f29e35f3da08e292c635a93f`):
  Stage 2 and § *Historical seal debt*.
- The **#248 seal ledger**: `briefs/pass-shelat-ch5-8/maintainer/cleanup-incremental-2026-11-09/final-r1/11-final-read-ledger.zip`
  (`7eb1dbea30829ba69117e756623d61d12c14395cf8cfdc41a51a4e17ea588d8f`), entry `deferred-read-ledger-final-r1.json`
  (`1c8124d912d71005a6a3ad8ecc10ae89dc256cca04bb3694b41dbf49fbad0faa`); its `README.md` beside it
  (`a2e0b18806c95814b282a2fd3a996808633b48583c97f06edc97fdedd52440dd`). The ledger head is #248's candidate
  `7750947a65d262b8a4e4e557b6dae2a48865807a` (base `b9f39f118efa40f4d76e0ebe8d7db59555b11735`); #248 merged at
  `e398d5cb7ead61a6946497af6bca6f26630b5f7b`.
- **The 2026-11-10 rulings:** `fills/efficiency/issued-r1/PROOF-DEPENDENCIES.json`
  (`088dc6f48324a41da0d7f2e3a653a551d207e7fd44c4df6831b58c8f6d89fbb8`, `named_api_ledger_overlap`: the 72) with
  `gates/10-efficiency/resolutions-r1.md` (`dfc802d5e5966748afe4d8b5eb077ec9b1c63a46b092c08e2a3fdc56f64a8f31`);
  `maintainer/proof-prerequisites-2026-11-10/provider-comparison.json`
  (`e236f87b2c49efe148d6bfd0a19aeab450c5c81b77c363923b61b4e97d18e2a0`, `levin`: the 52) with `provider-ruling.md`
  (`31f923c98402ddc67bd2eecda6f39bc5beb4c2ed520e22363a81e0d080d4b826`) and `gates/11-levin/verification.md`
  (`237ddca707da8e28e25c1a3821d95de28688b6df2598feca4a4cddacf755472a`).
- **SG-F07:** `gates/36-sc-garble/review.md` (`4e94a6efdaea13f58e3f6152ede337b3be8790a7923ca8e35df44ec2e114f226`),
  `gates/36-sc-garble/verification.zip` (`9051abffa8a66bf048ef4481f82e7d521c757c98c5582e7cf8e2f4deb44455ed`,
  `evidence/logs/seal-B-attribution.txt`). **SY-F07:** `fills/sc-yao/final-r1/review.md`
  (`413dff4ce90aabc08dbcaf1a302c71056e300c56077c60e88c75c06593ed37e8`), `gates/42-sc-yao/pack.md`
  (`58bfa0002cb794f00c48b7d8cc3305f3c8c9c3290623537d6e7453abbc997a19`) and `gates/42-sc-yao/verification.zip`
  (`4fed06a6b6c7718829ac62677b6aa87955d468fbdc66b27e133e03b04f93f92b`, `pack-checks/rule10-errors.txt`).
  **C-F02:** `gates/35-canonizer/review.md` (`beaaf7eadf3d8d62d8ec148587833d3471648a9710481a94d2073c22f64f43c1`) and
  `gates/35-canonizer/verification.zip` (`b4cd0af9b8db2c19cbcdd80f9a7019dfc03b8de6f420563f4dae12e50ab0f7fd`,
  `evidence/seal-full/`). (All paths under `briefs/pass-shelat-ch5-8/`.)
- **The Rule 10 suite as recent jobs ran it:** DW-5's `briefs/pass-shelat-ch5-8/maintenance/dw5/README.md`
  (`61918a0886407336f4e6af037f1883b8281ca49b5969291f2fae1f4cca3e1396`) and `dw5-evidence.zip`
  (`12abc05a61c08de7cb38b9d3bccdea5b3dd44dff6f65f036a50584a39e1dd630`, `dw5/tools-used/`: `rule10_dw5.sh`,
  `mkctl_dw5.py`, the `seal/` suite); bb1-sim's statement review `briefs/pairings/fills/bb1-sim/statements-final-r1/review.md`
  (`7bdb5967bf1469ae78d4cc0744e109645a40684c48b2e01247cc70ecd408fafa`).
- `policy.md` (`6599b12230e3879bc0e1fb22c0376ea6201bca8b7edd79dfc55da43986f991d4`) §1, *Definitions land with their
  lemmas* and *Reducible abbreviations are notation*; `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2, the standing
  rules (`d328d0d6e844b3429c0c500b5cdaad72f947c5941d56535362176ead25df9666`).
- `workflow.md` on `main` (`a954201d421a61994e02e36ff3cf4b16dce53f5d`; fetch `main` by name and read it with `git show`),
  §4.1 (the delivery payload) and §6.1 (the olean snapshot) (`917afe65ee154faea862905041d78a83bbb42b6738e0bcff5168a618bc7a8b83`).

**Exchange** `exchange/pass-shelat-ch5-8` at `d929cc21ec817b2518d57a7262e42744728f029a` (the parent of this job's
staging commit): `inbox/fills/bb1-sim-statements/evidence/tools/` (tree `e25f7bf0c9b78e764917868ad52a5f4044d0dcd2`,
delivered by `a3cb45f6a83c7308db5f2c5fcf95d25fc7f3fef9`): the most recent adaptation of the canonical suite
(`drivers/rule10_stmt.sh`, `seal/rule10_b.sh`, `seal/runner_full.py`, `seal/review/{mkcollect,mkseals_ab,mkseals_coe,
ctlcheck2,sealsum,touched}.py` with `NmCollect.template.lean` and `archived-gate10-tools/`, `seal/scan1_g40.py`,
`seal/scan2.py`, `seal/decls2.py`); and `inbox/fills/bb1-machine/evidence/tools/` (tree
`43455ee72a4b610ba5306bcff004e9d8c384455e`).

## Binding rules for this job

- **Checks only.** No file under `TCSlib/`, `audits/`, `scripts/` or the lakefile changes; nothing is committed to a
  Lean branch; nothing is re-pointed, repaired or deleted. Probe sources live in untracked probe directories (the
  addendum). A fix you see is recorded in the classification, not applied.
- **The base is pinned.** Fetch `cryptography/pass-shelat-ch2-4` by name; the issue base must be its tip or an
  ancestor of it. If a later records commit changes a `.lean` file, `lean-toolchain` or `lake-manifest.json`, say so
  in `REPORT.md` and keep the inventory at the base.
- **Standing rules.** Never `lake build`, never an unfiltered `lake exe cache get`; bootstrap one module at a time with
  `scripts/lean_check_tree.sh`; every probe through `runner_full.py` (`lean -DmaxErrors=0`, no `-o`); one Lean
  process at a time on the host, for all agents, through one lock (`flock <clone>/.lean.lock …`), released between
  modules; Python as `python3 -I`; full 40-character hashes from `git rev-parse`; count errors in both forms
  (`^\S+\.lean:\d+:\d+: error[:(]`) in every log; check every seal's install and EOF records (`requested = verified`;
  a log without its EOF record is an incomplete run, never a result: C-F02); keep every raw log.
- **No question is decided by the worker.** Where this brief leaves something open, follow it and report the question
  (`DW10-W1`, …, recommended option first).

## The Rule 10 canonical seal suite (what each check means here)

Adapt the bb1-sim tools (exchange, above) and DW-5's (`dw5/tools-used/`); copy what you use into `evidence/tools/`,
change host paths and the owner lists, and record every change in the tool's header. The archived Gate 06/10
instrumenter (`archived-gate10-tools/`) is used unmodified.

1. **Collector.** `mkcollect.py` over `NmCollect.template.lean`, one collector per batch of owners (at most about 100
   modules per collector; record the batches): `CAT` (every TCSlib definition with kind, reducibility and home),
   `ROOT` (every stored constant of each owner with its type and value references), `CLOSURE` (each owner's TCSlib
   import closure) and `COEINST` (projection-coercion instances) records. The collector is the authoritative list of
   each owner's declarations and of each item's location at the base.
2. **Seals A and B, strict and coe.** For each owner, a whole-file probe: the owner's source bytes (`git show
   <base>:<path>`) with the harness that installs `attribute [local irreducible]` on every ordinary TCSlib definition
   of its import closure (kind `def`, a matcher or not reducible); install and EOF records. **A** excludes
   `Complexity.PolyExpr.eval` (notation, ruling Q1 of 2026-11-07); **B** (`SEAL_EVAL=1`) seals it too. **Strict**
   (`mkseals_ab.py`) seals every request; **coe** (`mkseals_coe.py`) treats the projection-coercion instance
   `FinDist.instCoeFunForallReal` as notation (Q3, Seyoon 2026-11-17: the `FinDist.instCoeFunForallReal` coercion is
   notation). **Coe-A is canonical.** All four variants run and are recorded. Reducible abbreviations are never sealed
   (policy §1). Use `SEAL_CHUNK` (for example 2000) for any request set above about 2,500 rows (one harness command
   overflows Lean's stack at 2,921 rows); record it. **Variant deduplication:** where two variants of one owner
   generate byte-identical probe files (strict = coe when no `COEINST` instance is in the closure; A = B when
   `PolyExpr.eval` is not in it), run the probe once and record the SHA-256 equality; the result stands for both.
3. **Paired controls** on every owner that defines at least one TCSlib `def` (not an `abbrev`): one pair per owner,
   a negative that reads one of the owner's definitions from a probe by `rfl`, `unfold` or `show` (it must fail
   sealed exactly once and pass unsealed), and a positive that proves the same fact through that definition's
   published reader (`_eq`, `_apply`, `_iff`, `_def`, a `simps` projection or a contract lemma; it must pass sealed).
   Where the owner has no definition with a reader, run the negative only and record "no reader" (it is check 8 debt,
   not a seal failure). Batch the pairs into harnesses of about 25 owners each, strict and coe; pretest unsealed first;
   `ctlcheck2.py` per harness must give `ALL_OK True`. Owners that define nothing get no pair; say so.
4. **The explicit-unfold scan** (my choice for this job: **run it on every owner**, since it
   is a static pass plus one kinds probe per batch, far cheaper than the seals): `scan1_g40.py` with the archived
   `scan_explicit.py`, a kinds probe through `runner_full.py`, then `scan2.py`, with every declaration of the file
   treated as touched (`touched.py` over the whole file). Result: every foreign-definition item (a TCSlib definition
   of another file passed to `simp`, `rw`, `unfold` or `delta`, or read by `show`/`change`), attributed to its
   declaration, with local binders and own-file definitions separated out.
5. **Generated-equation reads**: from the collector's `ROOT` value references, every owner declaration whose stored
   value references a foreign TCSlib definition's `eq_N`, `eq_def` or `eq_unfold` (the #248 channel C3 and the
   historical `eqn-term` rows).
6. **Notation, never an item to fix:** reducible abbreviations (`ModuleHost.hostTMView`, `ModuleHost.State`,
   `QueryImpl`, `ProbComp`, `NUPPT.Coins`, `Turing.Cfg.Halted`, `IBEScheme.sidSpec`, …), the `FinDist` projection coercion
   (Q3, Seyoon 2026-11-17), and `PolyExpr.eval` (ruling Q1 of 2026-11-07). The strict and B variants seal the last two
   anyway; their failures are recorded, classed, and not fixed (B: separate ruling; strict: no fix).

## The owner set (`owners.txt`, `list-only.txt`)

| Set | Files | Seals A/B strict/coe | Controls | Scan | In the Stage 2 fix list |
|---|---|---|---|---|---|
| T1, created by the campaign | 414 | yes | yes | yes | yes |
| T2, adopted (Garg concrete layer, InformationTheory) | 20 | yes | yes | yes | yes |
| Facades (no declaration) | 24 | no | no | no | — |
| Handed off (outside the campaign, Q1) | 21 | no | no | no | no: their items are HANDED-OFF |
| Considered and excluded | 18 | no | no | no | — |

The derivation is in `owners.txt`'s header: origin by the base's first-parent history (`derivation/origins.py`), the
campaign's PRs and its 2026-10-28 layer commit for T1, P0's #183 for the two P0 files, Garg/InformationTheory files
changed by a campaign PR for T2, and cross-checks against the ch. 2–4 plan's module table, cleanup Stage 1's homes and
the #248 ledger's owners. GSW, pairings and IBE, the lattice LWE/SIS layer, Arora–Barak and Ladner files are excluded;
the 21 handed-off files are outside the campaign but hold recorded items, which this job carries as HANDED-OFF. **Check it:** if the collector
shows an owner with a different declaration count from `owners.txt` by more than the static scanner's known blind spots
(anonymous instances, `deriving`, `mutual` blocks), or you find a campaign file that the derivation missed (a file
created by a Pass–shelat PR that is not listed), report it as `DW10-W…`; do not change the set yourself.

**Where the items sit** (static mapping at the base; confirm with the collector):

| Source | Items | In owners | HANDED-OFF | No declaration at the base |
|---|---|---|---|---|
| #248 historical rows | 764 (seal 265, unfold 446, eqn-term 53) | 748 | 9 | 7 |
| #248 current observations | 813 (SEAL 465, C1 344, C3 4) | 374 | 437 | 2 |
| Provider pairs | 124 (75 SEAL ids) | 22 (efficiency) | 102 (50 efficiency, all 52 Levin) | 0 |
| SG-F07 / SY-F07 / C-F02 | 78 rows | 18 | 60 | 0 |

## Reconciliation: statuses

Each item of the four input tables gets exactly one **status**:
- **HANDED-OFF** (Q1): the item's declaration is in a handed-off file (`scope` = `HANDED-OFF`: 9 historical rows, 437
  current observations, 102 provider pairs, SY-F07's 2 `Uniform` rows and C-F02's 58 rows; 608 rows). It is not
  checked: copy the record into the row (`record`), leave the seal and scan columns `-`, and give it no class. If the
  collector shows the declaration elsewhere than `base_path`, say so in `change`.
- **FIXED_SINCE** (every other item, after the checks): the recorded failure is gone at the base in its channel (no seal error in the declaration in the
  item's variant and in coe-A; no matching scan item; no matching generated-equation reference). For a historical row
  #248 already marked repaired, FIXED_SINCE confirms it stayed fixed.
- **STILL_OPEN**: the same failure is present: same declaration, same channel, same provider (the definition read) and,
  for seals, the same failing step (by the probe-to-source line map and the message class) and count.
- **CHANGED**: the declaration still fails in the channel but differently (other provider, message class, count or
  variant, for example now B-only), or the item moved, was renamed or removed (`base_match` `moved`, `not-found`,
  confirmed with the collector), or a repaired row regressed. Give the change in a short phrase.

Matching by channel: `seal` rows and `SEAL` ids by the seals (all four variants recorded; #248's whole-file seals predate the
coe variant, so compare with strict A first, then give all four); `unfold` rows and `C1` ids by
the scan; `eqn-term` rows and `C3` ids by check 5; provider pairs take their `SEAL` id's status (one row per pair, so
124 rows; those of `HANDED-OFF` scope stay HANDED-OFF); named findings by the per-declaration counts of `named-findings.tsv` in the stated variant.

**New failures:** every seal failure (any variant), foreign scan item or generated-equation read at the base, in an owner,
that no input item matches, gets its own row with status **NEW**. Cascades (an error caused by an
earlier error in the same declaration) are attributed to the first error and marked `cascade`.

**Known later records (attribution aids, not inputs).** Some debt was recorded after #248; attribute NEW rows to these
where they match, and say so in the row:
- DW-9 (DW-5's README): `ModuleHost` 10 pre-existing failures (`stop_step`, `stop_clean`, `clean_install`,
  `clean_emit`, `pad_seam`, `pad_apply`, `pad_run`, `host_seam`, `host_call`) and `IterateFindHost` 16 (6 in the
  `copy_*` lemmas, 10 in the statements of `host_dispatch`, `host_branch` and `host_halt`), and 27 foreign scan items in
  `IterateFindHost`'s untouched proofs. Named for Stage 2 by `cleanup-stages.md`.
- F-01: `IterateFind`'s 20 failures (`computesFunInTime_find` 9, `polyTimeComputable_find` 11). **Cleared by #347
  (DW-5), open and not in the base:** record them as found at the base with `pending` = `#347`.
- BS-F06 (bb1-sim review): the strict seals of `Games/Probability` fail once at `ProbComp.dist_apply` (the `FinDist`
  coercion request); coe passes. Under Q3 it is STRICT-ONLY (notation, no fix).
- Gate 35: `Asymptotic/Universal` 10 (A) / 12 (B) pre-existing failures, identical at that gate's base and head.
- Gate 11: 311 untouched failures in the Levin owners, each identical at that gate's base; its explicit-reader scan
  put the inherited items in the excluded Arora–Barak files `TuringMachine/Build/Primitives`, `EmitIterBody` and
  `EmitIterEmbed`, and in `Randomized/Build/PairSplit` (an owner).

## Classification of open items

Every STILL_OPEN, CHANGED-and-failing and NEW item gets one **class**:
- **STAGE2**: fixable in cleanup Stage 2 by a reader or a proof-only re-derivation, in an owner file, without a
  statement change. Give the fix: the published reader to use (full name), or the reader to add and its home file
  (an owner).
- **STAGE2-PROVIDER-READER** (Q1): an owner's seal fails, or its scan finds a read, because a cryptography proof
  unfolds a definition of a file outside the campaign (a Complexity-library definition, for example in
  `ClassNP/PolyTime` or `TuringMachine/Build/Wrappers`), and the natural fix is a reader next to that definition.
  The item stays ours; name the **provider file** and the reader needed (its statement in one line), and say whether
  a published reader already exists there (then the item is STAGE2 instead). Seyoon decides where the reader lands.
- **SEAL-B-ONLY**: fails only under seal B (a `PolyExpr.eval` conversion or a cascade from one). Listed; separate
  ruling (DW-10).
- **STRICT-ONLY (notation, no fix)**: fails only under the strict variants, at the `FinDist.instCoeFunForallReal`
  coercion or a cascade from it. Q3, Seyoon 2026-11-17: the `FinDist.instCoeFunForallReal` coercion is notation, as
  `PolyExpr.eval` is under the ruling of 2026-11-07. No fix and no further ruling: recorded diagnostics only.
- **STATEMENT**: the canonical failure sits in a declaration's statement (its header reads a foreign definition, as
  DW-9's `host_*` statements do), so no proof-only fix exists under the statement freeze. Listed; separate ruling.
The class is the worker's assessment of the likely fix from the evidence (the read, the reader search, the statement);
it decides nothing. Where two classes apply, take STAGE2 if a Stage 2 fix exists, then STAGE2-PROVIDER-READER, then
the first that applies in this order, and note the other. HANDED-OFF items get no class.

## Feasibility and size (maintainer's assessment)

One job, long and mechanical, in one session with checkpoints. **434 owners: 1,736 seal probes before deduplication**
(4 variants each), plus about 18 control harnesses in each of strict and coe with their pretests, one collector and one
scan kinds probe per batch, and the 613-module bootstrap (the handed-off files are built, since the owners import
them, but not sealed). Requests: the static lower bound is **317,051 per variant**; recorded seals ran 1.65–2.0 times
the static count, so expect about 520,000–630,000 per variant, about 2.1–2.5 million over the four before
deduplication. The owners have 160,044 lines. Lean time is serial: the DW-5 replay averaged about 9 s per module, so
expect roughly 1.5–2 h for the bootstrap, 7–12 h for the seals (each seal re-elaborates its owner) and 1–2 h for
controls, collectors and scans. The heaviest single probe is the `Yao` hub (about 3,046 requests); use `SEAL_CHUNK`. If the job cannot finish in one session, deliver what is complete as
a checkpoint (with the remaining owners listed) and stop: a continuation brief follows.

## Branches, trees and delivery

- **Clone.** Your own clone of `https://github.com/Shilun-Allan-Li/tcslib`; fetch `cryptography/pass-shelat-ch2-4`,
  `main` and `exchange/pass-shelat-ch5-8` by name; record `git rev-parse` of each. A worktree detached at the base (the
  lead's) and one per sub-agent; sparse checkouts are fine. **No Lean branch is created or committed.**
- **One olean tree** (the addendum): the lead bootstraps `order.txt` at the base, records its object map, makes it
  read-only and rehashes it at the end.
- **Deliver** every checkpoint and the final only under `inbox/audits/dw10-seal-inventory/` on
  `exchange/pass-shelat-ch5-8`, from a local branch made from the exchange tip, committing with
  `git -c commit.gpgsign=false`:
  - `REPORT.md` (*Report*);
  - `inventory.tsv` (*Deliverables*);
  - `evidence/`, with its manifest `evidence/SHA256SUMS`;
  - a top-level `SHA256SUMS` of every delivered file except itself. The delivered paths must **equal** the manifests'
    paths: nothing missing, nothing extra, no leading `./`. Check before each push.
  There are no `patches/` or `src/`: the job changes no source (say so in `REPORT.md`).
- Commit on the exchange as `audit dw10-seal-inventory: checkpoint N` and `audit dw10-seal-inventory: final`. Pull with
  rebase before pushing; push only your path; never force-push; never touch another path (other jobs, `outbox/`,
  `archive/`, `arora-barak-ch3-4/`, `lwe-sis-constructions/`). Never push a campaign branch. If a push is refused, keep
  the commit and say so.
- **Checkpoint 1** as soon as the bootstrap, all collectors, and the seals and scan of every owner that holds an input
  item (the owners with `ledger_items_at_base` above 0 and the owners of `named-findings.tsv`) are done:
  `inventory.tsv` with a status for every input item (HANDED-OFF ones included; classes may still be blank), the seal and scan tables
  so far, and the bootstrap records. The final has everything.

## Multi-agent work (up to 2 sub-agents)

- **The lead owns the job:** the clone, the bootstrap and the olean tree, the lock, the collectors, the merge of the
  agents' tables, the reconciliation, the classification review, the delivery and `REPORT.md`. Only the lead runs
  `lake`, fetches the cache, commits and pushes.
- **Suggested split** (`owners.txt`, column `agent`; disjoint; record any other split):
  - lead: the 126 owners in `Complexity/`, `InformationTheory/`, `LearningTheory/` and `Cryptography/{Asymptotic,
    Candidates, Composability, Foundations, HardcoreBit, NumberTheory, OneWayFunctions}` (51,434 lines);
  - sub-agent A: the 146 owners in `Cryptography/{SecureComputation, ZeroKnowledge}` (51,746 lines);
  - sub-agent B: the 162 owners in `Cryptography/{Encryption, Authentication, Games, Hashing, Randomness,
    Implications, Pseudorandom}` (56,864 lines).
- Each sub-agent works in its own worktree and probe and evidence directories, reads the lead's olean tree read-only,
  runs every Lean process through the one lock, and hands its tables and logs to the lead. A file is reassigned only
  through the lead, after its owner has stopped. Sub-agent logs go under `evidence/subagents/<name>/`; `REPORT.md`
  records who did what.

## Checks and evidence

1. **Preflight, cache, bootstrap** (the addendum). Bootstrap `order.txt` (613 modules) at the base: rc 0, 0 errors in
   both forms, and the `sorry` warnings of exactly `base-sorries.txt` (22 declarations in 9 modules). Bind every built
   source to `SOURCE-SHA256SUMS` (`evidence/build/summary.txt`: module, rc, errors in both forms, `sorry` warnings,
   source hash). Record the tree's object map and its SHA-256.
2. **Collectors** (suite item 1), per batch: rc and the record counts; then **the owner check**: each owner's stored
   declarations against `owners.txt` (report differences), and each input item's declaration located (the `base_path`
   of the input tables confirmed or corrected).
3. **Seals** (suite item 2) of the 434 owners (not the handed-off files): `evidence/seals.tsv`, one row per owner and
   variant: path, tier, agent, variant, requests, rc, errors (both forms), install, EOF, failing declarations,
   deduplicated-with (or `-`), probe SHA-256; and `evidence/seal-decls.tsv`, one row per failing declaration and
   variant: path, declaration, variant, errors, first error line (source line), message class, providers read (from
   the message and the request rows).
4. **Controls** (suite item 3): `evidence/controls.tsv` per owner: definition, reader (or `no reader`), negative result,
   positive result, harness, `ALL_OK` per harness and variant.
5. **Scan** (suite item 4) and **generated-equation reads** (suite item 5): `evidence/scan.tsv` (path, declaration, line,
   tactic, item, kind, home, foreign yes/no) and `evidence/eqrefs.tsv`.
6. **Reconciliation and classification** (*Reconciliation*, *Classification*): `inventory.tsv`, then the totals and
   the Stage 2 fix list in `REPORT.md`.
7. **Tree restore check:** the olean tree rehashed against its map (0/0/0); `git status` clean in every worktree except
   the untracked probe directories.
8. **Evidence completeness:** every file that `evidence/SHA256SUMS` names is delivered: the tools used, the collector
   sources and logs, the seal and control probe sources (as `.lean.txt`, or in numbered ZIP parts of at most 90 MB,
   each with an entry list), every raw log and `results.jsonl`, the scan inputs and outputs, the sub-agents' logs.
   Deliver in several commits if needed; leave nothing out for size.

## Deliverables

**`inventory.tsv`** (tab-separated, UTF-8, one header line), one row per item: the 764 historical rows, the 813
current observations, the 124 provider pairs, the 78 named-finding rows, then the NEW rows. Columns:
`item_id` (`H:<row>`, the `SEAL`/`C1`/`C3` id, `EFF72:<id>`, `LEV52:<id>`, `SG-F07:<n>`, `SY-F07:<n>`, `C-F02:<n>`,
`NEW:<n>`), `source`, `channel` (`seal`, `unfold`, `eqn`), `base_path`, `tier` (`T1`, `T2`, `HANDED`), `declaration`
(full name at the base, from the collector), `record` (what the record says, one phrase), `strict_A`, `strict_B`,
`coe_A`, `coe_B` (error counts in that declaration, or `-`), `scan` (matching foreign items, or `-`), `status`,
`change`, `class` (one of the six classes, with `STRICT-ONLY (notation, no fix)` written out, or `-`),
`statement_level` (`yes`/`no`), `fix` (reader to use, reader to add with its home, the provider file and reader for
STAGE2-PROVIDER-READER, `none (notation)` for STRICT-ONLY, or the ruling needed), `pending` (`#347` or `-`), `known_record` (DW-9, F-01, BS-F06, Gate 35, Gate 11, or `-`), `evidence`
(log path and line).

**`REPORT.md`**:
- the base, the records tip and exchange tip used, the Lean equality check, the toolchain and Mathlib pins, the
  preflight figures, the olean tree map SHA-256 and its restore check;
- who did what; the batches; the tool changes;
- **totals**: owners sealed; probes run and deduplicated; requests per variant (sum, maximum);
  failing declarations and errors per variant and per tier; controls (pairs, `no reader` count, `ALL_OK`); scan items
  (foreign, per tier); a table of status by source (the four inputs, NEW; HANDED-OFF counts per source), a table of class by tier, and the counts
  for each of SG-F07, SY-F07, C-F02 against their records;
- **the Stage 2 fix list grouped by file**: for each owner file with STAGE2 items, its items (`item_id`, declaration,
  the read), the fix (reader to use, or reader to add with its home) and whether Stage 1 (dispatched, additive) or #347
  already supplies it; then the totals per file. STRICT-ONLY items are never in it;
- **the provider-reader list** (STAGE2-PROVIDER-READER), grouped by provider file: the reader needed, its one-line
  statement, and the owner items that need it (Seyoon decides placement);
- the lists for separate ruling: SEAL-B-ONLY and STATEMENT, by file;
- **STRICT-ONLY (notation, no fix)**: recorded diagnostics only (Q3), by file, with counts; no fix proposed;
- the HANDED-OFF items: counts per source and per file (the rows are in `inventory.tsv`);
- the NEW failures, by file, with their attribution;
- the owner check (step 2) and any owner-set question;
- questions for Seyoon, if any (`DW10-W1`, …, recommended option first);
- the evidence, with its manifest.

## Blockers: stop and report

- **E-RES (environment).** The addendum's preflight or cache rules fail. Stop and report the numbers.
- **E-BOOT.** A module of `order.txt` fails to elaborate at the base, or its admissions differ from
  `base-sorries.txt`. Stop the dependent checks (addendum item 8) and report the module and its log tail.
- **E-HARNESS.** A seal probe has no install or EOF record after `-DmaxErrors=0` and `SEAL_CHUNK`, or a control harness
  is not `ALL_OK`. Keep the logs, report the owner, and continue with the other owners.
- **E-SCOPE.** Anything that would need a source change, a branch commit, or a path outside `inbox/audits/
  dw10-seal-inventory/`. Do not do it; report it.
