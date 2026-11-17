# bb1-sim fill · final r1 · phase 2: landing branch and merged-tree replay on olean snapshot #5

**Verdict: PASS. The landing head `land/pairings-bb1-sim` `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff` is clear for its
draft PR.**
- The branch is the records tip plus maintainer-signed cherry-picks of the worker's 4 commits plus LE-bsf1. The picks
  applied cleanly; `range-diff` is 4/4 `=`; LE-bsf1 is byte-identical to the proposed diff.
- decls2 against the tip: **69 ADDED, 0 CHANGED, 0 REMOVED**. The reader pins `97ecb6e0…`/`88454d6f…` hold; the
  frozen-header check passes 12/12 with its 8 controls.
- The replay rebuilt **19/19 modules with rc 0**, 0 `error:`/`error(` and 0 `sorry`. The state check gives 1432/1432
  OK, every rebuilt olean has link count 1, and snapshot #5 rehashes 0/0/0 before, after the build and at the end.
- **Admissions against the tip: 196 → 192, exactly −4** (`expect_simulate_rel`, `expect_sample_rel`, T2, T3).
- **Axioms:** 76 constants, all standard; the census over the 9 owners is 325, 0 non-standard. **`bb1_sidSecure` is
  standard, and its `#sorry_trace` is empty** (closure 20,373), as are the traces of the five other roots.
- **Rule 10:** 36 canonical seals (A, B; strict, coe; 9 owners) with **0 errors**, request counts equal to the delivered
  table; paired controls **ALL_OK** in both harnesses (485 sealed negatives each failing exactly once, every positive
  and unsealed probe clean); explicit-unfold scan **0 foreign**. Lint is unchanged against the tip.

Run on 2026-11-17, 07:44–09:08 UTC. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Evidence:** `bb1-sim-fill-final-r1-phase2-evidence.zip`, under `bb1-sim-fill-final-r1-phase2/`, with
  `PROVENANCE.txt`, `SHA256SUMS` and this file. Its own SHA-256 is in `evidence-SHA256SUMS`.
- **Builds:** no `lake build`, no cache get. This job ran one Lean process at a time and checked the host's slot count
  (fewer than 3 `lean` processes) before every module and probe; it never had to wait.
- **Not touched:** the snapshot (read and hard-linked only), the other replay directories (`olean-replay-6a-*`) and other
  agents' directories. The records branch has no commit from this job.

## P2-0 Inputs
- **Records tip** (after `git fetch`): `origin/cryptography/pass-shelat-ch2-4` = `e1d39836ed4a69a34914c35f4c73c71de853dcc6`.
  `git diff` from `3f540c22360c869069a0fba684e23ce6f3cb20db` (the #346 merge, snapshot #5's T) over `*.lean`,
  `lakefile.lean`, `lake-manifest.json` and `lean-toolchain` is empty.
- **Delivery:** `inbox/fills/bb1-sim/` at exchange `2467bc3befdad8472b1f359337bf3a203e3651e1`, re-extracted by
  `git archive`; the 4 patches and `COMMITS.tsv` pass the delivery `SHA256SUMS` and equal phase 1's extraction.
- **Proposed LE-bsf1:** `le-bsf1-proposed.diff` from the phase-1 zip (zip `f74bcbde…`, `sha256sum -c` OK; internal
  `SHA256SUMS` OK). The diff is `8f18c2e3…43c5fe`.
- **Snapshot #5:** `$SP/olean-snapshot`; map `olean-snapshot.map-3f540c22.tsv` `fca1b6a3…41ef9`; files manifest
  `olean-snapshot.files-3f540c22.txt` `12457f32…c650`.
- **Tools:** the recipe's `olean-advance-a6d01b1b/tools-used/` from `olean-rebase-evidence.zip` (`b662b7da…`),
  byte-identical to the copies used; Gate 44's `tools/seal` harness; the phase-1 tools (`decls2.py` `fa81981a…`,
  `inscheck.py`, `frozencheck.py`, `hygiene.py`); the delivered `mkctl_bb1sim.py` and `Axioms.lean.txt`. New or adapted
  (all in `tools/`, each with a header naming its change):
  - `run-build-bsf.sh` (the recipe's `runner.py`, unmodified, called once per module behind the slot gate);
  - `rule10_bsf2.sh` (phases `statements`, `collect`, `axioms`, `seals`, `scan`; composed from Gate 44's
    `rule10_g44.sh` and the delivered `rule10_bb1sim.sh`);
  - `runner_full_gated.py` and `rule10_b_gated.sh`: `runner_full.py`/`rule10_b.sh` plus the slot gate only;
  - `mkctl_bsf2.py`: `mkctl_bb1sim.py` plus the two `bb1RealState_eq` entries (P2-5);
  - `inscheck_tip.py`: phase 1's `inscheck.py` with `BASE` set to the tip;
  - `sigfp.py`: reads the SSH key fingerprint of a commit signature (no `ssh-keygen` on this host).

## P2-1 Landing branch
- **`git am` reproduction** (sparse detached worktree at the patch base `72c0498a…`, committer and date per
  `COMMITS.tsv`, signing off): **4/4 REPRODUCED**, `23614c0a`, `3f430cae`, `622f5b03`,
  `c35595aef7636c2ba9a25e1ffdac141b08d2fea5`, none with a `gpgsig`.
- **Branch** `land/pairings-bb1-sim` from the tip, in a sparse worktree (`TCSlib/Cryptography/Games`,
  `…/AdvancedEncryption/IdentityBased`). `git cherry-pick -S` of the 4 commits applied cleanly, keeping author
  (Claude) and author dates:
  - `69fa787fc52a9c7dff34c8f448ed78b68fcbfbd1` (readers), `2845f1002f63f5ede2eed45e218e42c6b2e8e8e0` (`Relational`),
    `469375fa2d96ae6088c4c7a16b96724559084301` (helpers), `40f7da54d280a1e2bb48fc17c2555f089617a2c9` (T2/T3).
  - **LE-bsf1** `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`: `git apply` of the proposed diff, one signed commit whose
    message ends with the two required trailers.
- **Checks:**
  - `git range-diff 72c0498a..c35595ae e1d39836..40f7da54`: **4/4 `=`**.
  - `git diff 40f7da54 7a98ba01` is **byte-identical** to `le-bsf1-proposed.diff`.
  - At `40f7da54`, the 9 fill files equal `c35595ae`'s byte for byte. The tip differs from the patch base only by #340
    (`Pairing/Assumptions.lean`) and LE-g44 (`Draws`, `Words`, `Handler`), none of them a fill file.
  - The landing head's Lean, minus LE-bsf1, equals phase 1's T_land `c1d5fd89` (empty diff over `*.lean`, `audits`,
    the lake files). Against T44′ `bee027f0` the head differs in exactly the 9 files.
  - `git diff --stat e1d39836 7a98ba01`: 9 files, +1925/−21. No path outside the 9.
  - All 5 commits carry a `gpgsig`; each is an ed25519 signature by `SHA256:32dP45eSMmVSt/G/CGvcxl/P+MO3Nwj9xeTh/GSA2wc`,
    the key of the records commits (e.g. `e1d39836`). `git verify-commit` is unavailable here (the host's signing
    program does only `-Y sign`), so the key was read from the signature blob (`sigfp.log`).

## P2-2 Static checks at the landing head
- **decls2** (pinned `fa81981a`) against the tip over the 9 files: **69 ADDED, 0 CHANGED, 0 REMOVED** — the 10 readers,
  58 `BB1Sim.*` helpers and `BB1Sim.bb1RealState_eq`. With the location column dropped, it is phase 1's 68 rows plus
  exactly `bb1RealState_eq` (line numbers move by LE-bsf1's docstrings only).
- **Reader insertion** (`inscheck_tip.py --controls`, base = the tip): `Defs.lean` block `d6f8faf1` head
  **`97ecb6e0…`** (563 lines), `BonehBoyen.lean` block `967f2a30` head **`88454d6f…`** (760 lines); base hashes
  `4e220ead…`/`da875140…` hold at the tip, pure-insertion bytes, removal restores the tip, blank line before each
  block: **PASS**; 12/12 controls fail as they must. **The pins are unchanged:** #346's 7 readers were already in the
  patch base `72c0498a`, and the tip's `Defs.lean`/`BonehBoyen.lean` equal the patch base's.
- **Frozen headers** (`frozencheck.py` tip → head, `--controls`): H1–H4 **12/12 PASS**; 8 controls fail as they must;
  the unchanged head passes.
- **Hygiene** (`hygiene.py`): every file ≤ 760 lines, no line over 100 characters, no `@[simp]`, no new `attribute`
  (`BonehBoyen.lean:386` is the base's), no micro sign, 0 `sorry`/`admit`/`native_decide`/`axiom` tokens. **Every
  helper docstring now has a `[BB04, …]` tag or a glue note** and a formula. The only `no-tag/glue` rows are the three
  frozen `Relational` statement docstrings of #351 (`expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel`),
  which phase 1 also listed and which this fill may not edit.

## P2-3 Replay (snapshots.md job recipe)
- **Copy and overlay:** `cp -al $SP/olean-snapshot $SP/olean-replay-bb1sim` (1458 files, all hard links);
  `mloverlay.sh` made 3346 symlinks; `mathlibextra.sh` built NthRootLemmas with rc 0, olean **`c0a9cff0…`**.
- **Tree:** `git archive` of `7a98ba01` (`TCSlib`, `TCSlib.lean`, `audits`, `scripts`, lake files, `lean-toolchain`;
  1584 files) with `.lake/packages` symlinked.
- **Plan:** `stateplan init` at `3f540c22`: 1427 modules. `downorder.py`: changed 9, **down 19**. `fullorder.py`: **1432**
  (roots `TCSlib` and both `audits/*/Checks`). `stateplan plan`: **19 to build, 1413 reused** — the 13 `DOWN` modules
  of `closures.txt` (`Relational`, `Games`, `Defs`, `BonehBoyen`, `BBM/{Draws,Words,Handler,Reduction,Oracles}`,
  `BonehBoyenMachine`, `BonehBoyenSecurity`, `IdentityBased`, `AdvancedEncryption`), the 5 helpers before
  `BonehBoyenSecurity`, and root `TCSlib`. Neither `Checks` is downstream.
- **Build** (07:48:00–07:49:44): **19/19 rc 0**; `error:` 0, `error(` 0, substring "error" 0, `sorry` 0, warnings 0;
  no log/record mismatch (`permod.py`). Sources bound to `7a98ba01` 19/19.

## P2-4 Accept (recipe step 5)
- `stateplan update`: 19 modules, none left out. `check` over the full order: **1432/1432, RESULT OK**, again at the end.
- **Link count 1** for all 19 rebuilt oleans (plus the NthRootLemmas olean); every other file is a hard link to the
  snapshot.
- **Snapshot #5** `snapmap.py verify`: **0/0/0**, 1458 files, no symlinks — before the copy, after the build and at the
  end.
- **Output map** (`mapnoml.py`, Mathlib excluded): **1463 entries** (1458 + 5), SHA-256
  **`b43812d0008b290343fab435f725544b1eef2c944f3581f2e8a62b3c0362171a`**. Against snapshot #5's map: 1454 equal,
  4 changed (`Relational`, `Defs`, `BonehBoyen`, `BonehBoyenSecurity`), 5 added (the helpers), 0 removed. The other 10
  rebuilt modules produced byte-identical oleans. The map is unchanged after all probes (they write no olean).
- **Admissions** (`tipcensus.py`, Gate 44's record sets plus this build): tip `e1d39836` **196**, head **192**. The only
  changes are `Relational` 2 → 0 and `BonehBoyenSecurity` 2 → 0 (plus the 5 new helpers at 0). The tip's four
  admissions are exactly `expect_simulate_rel`, `expect_sample_rel`, `bb1_sim_real` and `bb1_sim_random`.

## P2-5 Axioms and Rule 10
- **Axioms** (`AxiomsBsf.lean`: the delivered probe plus `bb1RealState_eq` and a sorry control; rc 0, 0 errors; its one
  `sorry` warning is the control's):
  - `AXIOMS-LIST 76 constants, 0 non-standard` (every new constant, the 4 targets, `prob_simulate_rel`,
    `bb1_sidSecure`, T4 `exists_bb1_distinguisher`).
  - Census: `Relational` 3, `Defs` 96, `BonehBoyen` 147, `BonehBoyenSecurity` 3, `Lazy` 24, **`Real` 29**, `Coupling` 20,
    `Random` 2, `Chain` 1 = **325, 0 non-standard**.
  - **`#sorry_trace`: no direct `sorryAx` user** for `bb1_sidSecure` (closure 20,373), `bb1_sim_real` (15,352),
    `bb1_sim_random` (13,412), `expect_simulate_rel` (5,020), `expect_sample_rel` (11,705), `prob_simulate_rel` (5,023);
    `collectAxioms` gives `bb1_sidSecure` the standard three. With #340 merged, T1 is proved, so nothing remains.
  - **Control:** `bsfSorryControl` is reported as its own direct `sorryAx` user and `NONSTANDARD [sorryAx]`.
- **Seals** (canonical, `mkseals_ab`/`mkseals_coe`, A and B with `SEAL_EVAL=1` for B, on the 9 owners; `sealsum.py`):
  **36/36 rc 0 with 0 errors**, install and end records present. Requests (A/B/coe-A/coe-B): `Relational` 53/53/52/52,
  `Defs` 805/806/804/805, `BonehBoyen` 840/841/839/840, `BonehBoyenSecurity` 2320/2321/2319/2320, `Lazy` 868/869/867/868,
  `Real` 871/872/870/871, `Coupling` 874/875/873/874, `Random` 871/872/870/871, `Chain` 877/878/876/877. The sealsum
  tables equal the delivered ones (columns 1–6) in all four variants; the mkseals records differ only in `Real`'s
  stored-constant count, 28 → 29 (`bb1RealState_eq`). LE-bsf1 adds no definition, so no request changes.
- **Paired controls** (`mkctl_bsf2.py`; `ctlcheck2.py`): 32 probes per harness (16 sealed, 16 unsealed), the same
  covering subset as the delivery. **strict and coe: ALL_OK**; **485 sealed negatives, each failing exactly once**;
  1479 positive or unsealed entries with 0 errors; 0 stray errors. Rows exercised include the 10 reader pairs
  (`SidZeroSpec`, `SidTwoSpec`, `SidOneQuery`, `SidTwoQuery`, `SidKeyNe`, `SidFresh`, `SetupEq`, `KeyGenBind`, `EncBind`,
  `EncCT`) and the 5 helper-definition pairs (`SimLazy`, `SimLazyChal`, `RealAt`, `RealLazy`, `RelM`). Every probe's
  per-control outcome equals the delivered `ctlcheck` exactly, apart from the new entries.
  - **`bb1RealState_eq`:** `BB1Sim.BB1RealState` is an `abbrev` and appears in **0 of the 36** request sets (the
    canonical seals never request abbrevs), so no sealed negative can exist for it — BSF-F02's "notation". The two
    entries `ctlRealState` (the unfolding by `rfl`) and `ctlRealStateReader` (the reader), attached to the `bb1RealAt`
    row, ran in 6 sealed and 6 unsealed probes per harness with 0 errors: the reader elaborates and states the
    abbrev's unfolding under every consumer's seal.
  - `RealReads` still has no pair (BSF-F05, accepted).
- **Explicit-unfold scan** (`scan1_g40.py`, `scan2.py`): **527 items** — 426 theorems, 85 local hypotheses or
  projections, 14 owned definitions, 2 `↓reduceIte` — **0 foreign**, identical to the delivered summary.
- **Attempt 1 of the seals phase** failed before any Lean ran: the seal generators call `git -C <tree> show`, and the
  export is not a repository. The driver now exports `GIT_DIR` (read-only use); the failed output is kept as
  `rule10/attempt1/`.

## P2-6 Lint
- `campaign_style_lint --check8b TCSlib/Cryptography`: tip **92 FAIL / 104 WARN over 524 files**, head **92/104 over 529**;
  the FAIL/WARN line sets are equal (0 new, 0 gone). The only IBE line is the base's `SIDSecure` WARN. INFO changes are
  the 9 files' line and declaration counts and the 5 new files.
- `style_lint` over the 9 files: 0 findings. `sk15`: one finding, `BonehBoyen.lean:677 bb1SimChal_fresh`, the base's
  (T4's) code.

## P2-7 State after the run
- **`$SP/olean-replay-bb1sim`** is kept as the snapshot candidate: 1464 files (1458 + 5 helpers + the NthRootLemmas
  overlay olean) and 3346 Mathlib symlinks. It is adoptable as snapshot #6 when the PR merges, if the merge's Lean
  equals `7a98ba01`'s (step-3 diff empty); adoption removes `Mathlib/` and should reproduce map `b43812d0…`.
- Kept for the PR: the landing worktree `$SP/bsp2/landwt` (branch `land/pairings-bb1-sim`). Removed at the end: the
  `git am` worktree and the build export. Phase 1's extraction `$SP/bsf-final/deliv/` was deleted as allowed.
- Raw seal records, control sources and probe logs (about 140 MB) are not in the zip; their SHA-256 are in
  `rule10/omitted-SHA256SUMS` and `scan/omitted-SHA256SUMS`, and the files stay under `$SP/bsp2/run/`.
