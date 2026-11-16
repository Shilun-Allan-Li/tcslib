# Fill `bb1-machine`: T4 `exists_bb1_distinguisher` — checkpoint 1 (readers and T4)

External Claude fill (lead plus one sub-agent), 2026-11-16 UTC, from the issued pack at exchange commit
`78d89c5cda437ae1bea629328eb3116e2f36d026` (`outbox/fills/bb1-machine/`).

**Status: T4 is proved.** `exists_bb1_distinguisher` has no `sorry`, and `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`. The seven approved readers are in their owners as pure insertions,
byte for byte. The glue is in a new helper module, `BonehBoyenMachine/Oracles.lean`. No statement is weakened, no
admission is added, and no frozen file changes beyond the seven insertions. There is no blocker and no new scope
request.

This is **checkpoint 1**, steps 1–4 of the brief. It carries the native sweep of the whole order (with the new
helper), the axioms of T4 and of the readers, the dependency trace, the reader-insertion check, and also the
statements diff, the frozen-header check, lint and the name-clash scan. The canonical Rule 10 seals and controls,
the base seals, and the unfold scan follow in the final.

## Base and branch

- Issue base `7c0a55e0239c14786612d0cd4462e64238543ca1` (`git rev-parse HEAD` after the checkout), the tip of
  `fill/pairings-bb1-machine`: three signed in-house checkpoint commits on #331's head `9e7a9648…`. They are not
  rewritten, and are not in `patches/`.
- Local branch `fill/bb1-machine` in a separate clone (`/home/user/fill/tcslib`). It was not pushed.
- Series on top of the base (`patches/`, `patches/COMMITS.tsv`). Committed with `git -c commit.gpgsign=false`;
  none is signed (`signing` = `none`):
  1. `633dcf99907e26fe5e1573f4c215d9b57585bf28` `bb1-machine: approved readers (scope request, Seyoon 2026-11-16)`.
     The readers alone.
  2. `b9a242ea050cd2eb026e8fe9dd3889974952bfa6` `bb1-machine: helper module Oracles (the glue, moved from
     MachineProbeMin)`.
  3. `c90273fad3511ada7c9c1a53e1abdd8478237cee` `bb1-machine: prove the BB1 reduction machine (T4)`.
- **Earlier, never-delivered versions of commits 2–3.** `40ae75456` and `297b06298` were the first versions of
  commits 2 and 3. `style_lint.py` then flagged `Oracles.lean`'s module docstring for a missing
  `## Main definitions`. Both commits were rebuilt on `633dcf99` with that heading (`None.`) added, and nothing else
  changed. A sweep begun at `297b06298` was stopped after 24 modules; it is kept in `evidence/build/aborted/`.
- Reproduction: `git am` of `patches/*.patch` at the base, in a scratch clone, reproduces every hash
  (`evidence/delivery/am-check.out`).

## Who did what

- **Lead (this session):**
  - every Lean edit, commit, `lake` command (the narrowed cache fetch only) and Lean run;
  - the build, sweep, axioms and seal runs;
  - the adapted runners and drivers, the reader control rows (`mkctl_bb1m_readers.py`), the statements, lint and
    width runs, `REPORT.md` and the delivery.
- **Sub-agent `tools-agent`:** ran no Lean, no `lake` and no git writes, and wrote only under its own directories.
  It built:
  - the reader-insertion check and its controls (`evidence/headers/insertion/`);
  - the adapted frozen-header check and its controls (`evidence/headers/frozen/`);
  - the name-clash scan (`evidence/clash/`);
  - the overlap searches (`evidence/overlap/`).

  Its log is `evidence/subagents/tools-agent/log.md`, with `files.sha256` covering the 97 files it created. The
  lead ran its tools on the delivered head; those outputs are in the `final-c90273fad/` subdirectories.

## Environment (addendum)

- **Preflight** (`evidence/logs/preflight.log`):
  - `nproc` 4;
  - cgroup v1 memory limit 14,338,772,992 B; headroom = limit − (usage − total_cache + total_shmem) = **13.09 GiB**;
  - the clone's filesystem is ext4 (`/dev/vda`), with **20.65 GiB** free.
- **Toolchain:** elan, then Lean 4.25.0 (`evidence/logs/toolchain.log`). Re-check before the cache: 12.65 GiB free
  (floor 8 GiB; `precache-recheck.log`).
- **Cache:**
  - The archive store `~/.cache/mathlib` did not exist before the fetch (`cache-store.log`).
  - Roots: 94, computed from `order.txt` by the addendum's command and equal to the pack's `roots.txt`
    (`mathlib-roots.txt`).
  - `lake exe cache get <roots>` with `TAR_OPTIONS=--no-same-owner`: "Attempting to download 2339 file(s)",
    2339 downloaded, "Decompressing 2339 file(s)", exit 0 (`cache-get.log`).
  - Zero-size oleans: none (`cache-check.log`).
  - Packages check: every present package matches its manifest URL and revision; `doc-gen4`, `UnicodeBasic`,
    `BibtexQuery` and `MD4Lean` are ABSENT. Last line: `PACKAGES-CHECK PASS (every present package matches its
    manifest URL and revision)`.
  - Cache probe (`import Mathlib.Algebra.BigOperators.Field`, the first root) through `lean_check_tree.sh`: rc 0.
- **One Lean process at a time.** Every `lean` and `lean_check_tree.sh` call ran under `flock` on
  `/home/user/fill/tcslib/.lean.lock`, taken per module (adapted `runner.py`, `runner_full.py`). The sub-agent ran no
  Lean. No `lake build`, and no unfiltered cache get.
- **Bootstrap** (`evidence/build/bootstrap-readers/`): the whole `order.txt` (188 modules) in order at the readers
  commit `633dcf99`: rc 0 for all, 0 errors in both forms, 57 `sorry` warnings in 18 modules (the base set). Peak
  RSS 2,924 MiB.

## What changed

Line counts are given at #331 (`9e7a9648`), at the issue base, and at the head.

| File | `9e7a9648` | base | head | Change in this series |
|---|---|---|---|---|
| `IdentityBased/Defs.lean` | 433 | 433 | 476 | the 3 readers, approved lines 27–68, after `oracleImpl_two` |
| `IdentityBased/BonehBoyen.lean` | 677 | 677 | 714 | the readers of approved lines 74–97 after the `simps` attribute; lines 99–109 after `bb1SimCt_eq` |
| `IdentityBased/BonehBoyenMachine/Oracles.lean` | — | — | 373 | **new** helper: the glue |
| `IdentityBased/BonehBoyenMachine.lean` | 85 | 100 | 137 | the `Oracles` import; one `## Contents` bullet; T4's `**Proof sketch.**` paragraph; T4's body |
| `BonehBoyenMachine/{Draws,Words,Handler,Reduction}.lean` | — | 451/632/899/243 | unchanged | none |

- **The readers.** Final SHA-256s: `Defs.lean` `4e220ead…`, `BonehBoyen.lean` `da875140…`, as the brief requires.
  Removing the seven blocks gives the base byte for byte (`evidence/headers/insertion/`).
- **`Oracles.lean`** (imports only `BonehBoyenMachine.Reduction`; namespace `…IdentityBased.BB1Machine`). It holds
  the probe `MachineProbeMin.lean.txt`, lines 16–294, as follows:
  - six private lemmas: `cast_eq_padFin`, `ofFn_padFin_ofFn`, `ofFn_decAnswer_some`, `sidSpec_rng_one'`,
    `sidSpec_rng_two'`, and `expect_bb1SimImpl` (section `Glue`);
  - one public lemma, **`abs_expect_bb1Sim_sub_distinguisherL_le`** (the probe's `abs_inner_le`), with a formula
    docstring, a `**Proof sketch.**` and a `## Main results` entry. `expect_bb1SimImpl` got a formula docstring, a
    `**Proof sketch.**` and step comments.
  - The probe's four lines over 100 characters (34, 40, 216, 246) are rewrapped. The tactic proofs are the probe's
    otherwise.
  - No new import is needed or used. `Oracles` is inserted into the build order after `Reduction`
    (`evidence/build/order-final.txt`, 189 modules).
- **T4.**
  - The `sorry` is replaced by the probe's proof (lines 296–323), with step comments, calling the moved lemma by
    its new name.
  - The `**Proof sketch.**` paragraph is rewritten to the delivered proof. It covers:
    - `D_b` from `Games.exists_handlerMachine` on `A'` from `Games.exists_toCompOn_of_toComp`;
    - the handler (algorithm `B` on encodings);
    - `n = κ + wG(κ) + 1` and `(Candidates.sampleBelowL p (Nat.size p) n n w).getD 0` on blocks of `n²` bits;
    - `σ(κ) = (q(κ) + 1) · 2^{−κ}`;
    - the four `ProbComp.abs_expect_sub_le` steps down to one tuple;
    - the per-call identity of `bb1SimImpl` with fresh exponents, through the seven readers;
    - the draws' bound `q(κ) · (1/2)^n ≤ σ(κ)`.

    The sketch speaks of the two probabilities differing "by at most", consistent with BB04's absolute-value
    advantage (LE-doc-abs).
  - Byte-identical, as checked: T4's header, everything before `**Proof sketch.**` in its docstring, and the rest of
    the file except the permitted import line and `## Contents` bullet.

## New declarations

| Name | File | Visibility |
|---|---|---|
| `IBEScheme.oracleImpl_zero_onSpec`, `_one_onSpec`, `_two_onSpec` | `Defs.lean:391`, `:405`, `:419` | public (approved readers) |
| `ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK`, `bb1Scheme_msgSpace_iff` | `BonehBoyen.lean:391`, `:400`, `:408` | public (approved readers) |
| `ofFn_bb1SimCt` | `BonehBoyen.lean:580` | public (approved reader) |
| `BB1Machine.abs_expect_bb1Sim_sub_distinguisherL_le` | `Oracles.lean:330` | public |
| `BB1Machine.cast_eq_padFin`, `ofFn_padFin_ofFn`, `ofFn_decAnswer_some`, `sidSpec_rng_one'`, `sidSpec_rng_two'`, `expect_bb1SimImpl` | `Oracles.lean:58`–`110` | private |

No new definitions, no `@[simp]`, no attributes.

## Checks (checkpoint 1)

| Check | Result | Evidence |
|---|---|---|
| Native sweep of the whole order with `Oracles` (189 modules) at `c90273fa` | rc 0 for all; 0 errors (`error:` and `error(`); 0 `error` substrings; sources bound to `git show HEAD` 189/189 | `build/sweep-cp1/` (`summary.txt`) |
| Admissions | 56 `sorry` warnings in 17 modules. The only change from `base-sorries.txt` (57 in 18) is the removal of T4 (`BonehBoyenMachine`). T1 (`Pairing/Assumptions`), T2 and T3 (`BonehBoyenSecurity`) remain. | `build/sweep-cp1/summary.txt` |
| Axioms census (all stored constants of the 8 changed owners) | 571 constants, 0 non-standard | `axioms/runs/` |
| `#print axioms` | T4 and `abs_expect_bb1Sim_sub_distinguisherL_le`: `[propext, Classical.choice, Quot.sound]`. The three `oracleImpl_*_onSpec`: `[propext, Quot.sound]`. The four BonehBoyen readers: the standard three. `bb1_sidSecure`: adds `sorryAx` | `axioms/runs/` |
| Dependency trace (constant closure through types and values) | T4: 19,638 constants, 0 sorried. `bb1_sidSecure`: exactly `bb1_sim_random` and `bb1_sim_real`. Positive controls: `bb1_sim_real` and `bb1_sim_random` each report themselves | `axioms/Axioms.lean.txt`, `axioms/runs/` |
| Reader insertion | `RESULT PASS`, 24/24 checks; ADDED 43 + 37 lines, REMOVED 0, CHANGED 0. Controls (12) `ALL_CONTROLS_OK True`: a changed character gives FAIL with exactly one difference; a deleted reader gives exactly one removal; an extra line in either file, a moved reader and an edited docstring each give FAIL | `headers/insertion/final-c90273fad/` |
| Frozen header of `BonehBoyenMachine.lean` (base `9e7a9648`) | PASS. Controls (17) all FAIL as required: the original 8, plus sketch spills into the prose (2), unpermitted `## Contents` changes (5), and a misplaced `Oracles` import (2) | `headers/frozen/final-c90273fad/` |
| T4 header and statement prose | byte-identical at `9e7a9648`, `7c0a55e0` and HEAD | `headers/t4/t4-header.out` |
| Statements (`decls2.py`) | Against `9e7a9648`: 174 ADDED (the checkpoint's 166, the 7 readers, the new public lemma), 0 CHANGED, 0 REMOVED. Against `7c0a55e0`: 8 ADDED (the 7 readers and `abs_expect_bb1Sim_sub_distinguisherL_le`), 0 CHANGED, 0 REMOVED | `statements/` |
| `touched.py` | Against `7c0a55e0`: 7 ADDED (readers), 7 NEW_FILE (`Oracles`), 1 CHANGED (T4, whose body and sketch change as permitted), 324 UNCHANGED. T4's header itself: UNCHANGED (`t4-header.out`, `decls2`) | `statements/touched-*.tsv` |
| Name clash (`TCSlib/`, `audits/` at `7c0a55e0`) | 14 new names (8 public, 6 private), 0 clashes, 0 same-short-name | `clash/final-7c0a55e0..c90273fad/` |
| Lint | `campaign_style_lint.py TCSlib/Cryptography --check8b`: base and head both 92 FAIL / 103 WARN; non-INFO line sets identical (empty diff); files 400 → 401 | `lint/` |
| `style_lint.py` on the 8 PR files | 0 findings | `lint/style-lint-files.txt` |
| `dev/sk15.py` | One hit: `bb1SimChal_fresh` (`BonehBoyen.lean:631`), which is frozen. It is pre-existing: the same hit is at the base (line 594), and the change is outside this fill's scope. No hit in the new code | `lint/proof-sketch-15.txt` |
| Widths and sizes | 0 lines over 100 in the 8 PR files; largest file `Handler.lean` (899, unchanged) | `lint/width.txt` |

## Overlap and reuse

Searches: `evidence/overlap/search.log` (every command and its output) and `overlap.md`.

**Carried forward from the checkpoint (items 1–7, unchanged):**
1. round-input readers (`Words.lean`) versus `InteractiveHandler.rU`, … and the Lamport readers;
2. residue arithmetic versus the private `DiscreteLogHardcore`/RSA/Rabin compositions and
   `FromDiscreteLog.modularDifference`;
3. group operations on encodings versus the `Ops` contract fields;
4. `draw`, `statClose_draw` and `poly_uS` versus `expSampleRaw`, `ddhExpo`, `ddhExpo_statClose` and
   `polyTimeComputable_expSampleRaw`;
5. `drawStep` versus `bb1SimInit`, `bb1SimKeyQ`, `bb1SimChal` (proving them agree call by call is the glue below);
6. reused, not redefined: tapes, casts, T1, expectations, `OneWay.statClose_pi`, `FunFamily.blocks`;
7. the private one-liners `expect_sample_eq_uprob` and `ite_ofFn_one`.

See the checkpoint's `REPORT.md` (`outbox/fills/bb1-machine/checkpoint/REPORT.md`) for each item's detail.

**New in this series.**

| Declaration | Nearest relative (`path:line` at the head) | Relation | Why not reused |
|---|---|---|---|
| `IBEScheme.oracleImpl_{zero,one,two}_onSpec` | `IBEScheme.oracleImpl_zero/_one/_two` (`IdentityBased/Defs.lean:363`, `:372`, `:381`) | restate them at the game's query type `(S.sidSpec κ).dom i`, with the casts both ways | the old readers take `x` at the handlers' types; using them at `(S.sidSpec κ).dom i` needs `inLens` unfolded (sealed). The `_onSpec` convention follows `FixedLengthScheme.indImpl_*_onSpec` (`Encryption/PrivateKey/OracleSecurity.lean:302`, …). Approved by Seyoon |
| `ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK` | the `simps` lemmas `bb1Scheme_encPP`, `bb1Scheme_encSK` (generated by `attribute [simps …] bb1Scheme`, `BonehBoyen.lean:386–387`) | word forms (`List.ofFn`) at `⟨d, pp⟩`/`⟨d, k⟩` | the `simps` lemmas state the lengths literally and the parameters as `Sigma` projections; rewriting with them gives an ill-typed motive at `Fin ((bb1Scheme G ℓ).ppLen.eval κ) → Bool` (checkpoint's scope request). Approved |
| `bb1Scheme_msgSpace_iff` | `simps` lemma `bb1Scheme_MsgSpace` (generated); `List.ofFn_inj` (Mathlib `Data/List/OfFn.lean`) | word form `⟦encT u⟧ = ⟦m⟧` of the message-space test | as above. Approved |
| `ofFn_bb1SimCt` | `bb1SimCt_eq` (`BonehBoyen.lean:573`); `simps` lemma `bb1Scheme_encCT` | word form with `encCT` unfolded (owner-side) | `encCT` of `bb1Scheme` cannot be read under the seals. Approved |
| `BB1Machine.cast_eq_padFin` (private) | `ofFn_cast` (`Asymptotic/Adversary.lean:225`); `padFin_ofFn` (`:211`); inline `have hm'` in `Encryption/PrivateKey/OracleFromPRF/Transfer.lean:73` and `…/EncryptThenTag/Transfer.lean:88` | `cast h f = padFin c ⟦f⟧` follows from `ofFn_cast` with `padFin_ofFn`; the inline `hm'` are instances | no public `cast … = padFin …` lemma exists. A two-line private helper, proved from the published `padFin_ofFn` and core `cast_eq` |
| `BB1Machine.ofFn_padFin_ofFn` (private) | `ofFn_padFin_of_length` (`Asymptotic/Adversary.lean:216`); private `ofFn_padFin_msg` (`Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean:645`) | specializes `ofFn_padFin_of_length` at `w = ⟦v⟧`, with a one-line proof from it; `ofFn_padFin_msg` is another instance | kept as a one-line private abbreviation for its 7 uses; not a re-proof (G24-01 style: disclosed) |
| `BB1Machine.ofFn_decAnswer_some` (private) | `FixedLengthScheme.decAnswer_some` (`Encryption/PrivateKey/OracleSecurity.lean:166`); Mathlib `List.ofFn_cons`; the inline steps in private `ofFn_prf_decAnswer` (`…/OracleFromPRF.lean:178`) and `ofFn_cca_decAnswer` (`…/EncryptThenTag.lean:509`) | `decAnswer_some` read as a word; the two private lemmas re-prove the same step inline | no published word form of `decAnswer (some v)` exists |
| `BB1Machine.sidSpec_rng_one'`, `sidSpec_rng_two'` (private) | `FixedLengthScheme.indSpec_decRng`, `indSpec_challengeRng` (`Encryption/PrivateKey/OracleSecurity.lean:285`, `:295`); the same propositions inline as `show … from rfl` inside the readers (`Defs.lean:413`, `:428`) | the IBE analogues, derived from `sidSpec_eq`, `bitSpec_rng` and `outLens_*` as the brief requires | `IBEScheme` publishes no such equation (the 13-reader variant that would add them is not approved); see *Promotion requests* |
| `BB1Machine.expect_bb1SimImpl` (private) | `ProbComp.expect_simulate_congr` (`Games/Hopping.lean:384`), whose hypothesis it discharges; `expect_indImpl_fImpl` (`…/OracleFromPRF/Transfer.lean:48`), `expect_indImpl_ettImpl` (`…/EncryptThenTag/Transfer.lean:65`) | the per-call step for BB1 (same shape as the other schemes'); uses the `bb1Sim*` and `drawStep_*` case lemmas without restating them | specific to `bb1SimImpl` |
| inline `have hq` in `expect_bb1SimImpl` (three cases) | `BB1Machine.qLen_eval` (`BonehBoyenMachine/Draws.lean:105`) | pointwise form of `qLen_eval`, proved from `inLens_*` and `qLen_*` | kept as in the checked probe |
| inline `have hzero` (two cases) | `padFin_ofFn_zeroBits` (`Games/BitCodec.lean:139`) | its left side is `zeroBits _` by `padFin_ofFn_zeroBits`; proved by `ofFn_zeroBits` and `padFin_replicate_false` | kept as in the checked probe |
| `BB1Machine.abs_expect_bb1Sim_sub_distinguisherL_le` | `BB1Machine.abs_expect_runAccept_sub_le`, `expect_handlerMachine`, `expect_castImpl_freshImpl` (`BonehBoyenMachine/Reduction.lean`) | new: composes them | no lemma states this bound |

The checkpoint's private `expect_sample_eq_uprob` and `ite_ofFn_one` are neither used nor restated by the glue.

## Scope requests

None in this job. The seven readers are the approved scope request of the in-house checkpoint (Seyoon, 2026-11-16,
minimal form), inserted verbatim. No other frozen file is changed.

## Promotion requests

- `IBEScheme.sidSpec_rng_one`/`sidSpec_rng_two` (and the `dom` analogues): the IBE counterparts of
  `FixedLengthScheme.indSpec_decRng`/`indSpec_challengeRng`. They are now private in `Oracles.lean` as
  `sidSpec_rng_one'`/`_two'`. They belong in `IdentityBased/Defs.lean`. **Not requested for this PR**: the 13-reader
  variant was not approved. This is recorded for a later decision only.

## Not yet in this checkpoint (final)

- Canonical seals A and B, strict and coe (coe A canonical), of the 8 changed owners, with paired controls
  (`mkctl_bb1m_readers.py`: `mkctl_bb1m.py` plus the 7 reader rows, pretested unsealed).
- The base seals of `Defs` and `BonehBoyen` at `7c0a55e0`.
- The explicit-unfold scan.
- The final pruning of `evidence/tools/` to the tools used, with each adaptation recorded.

## Evidence

`evidence/SHA256SUMS` lists every evidence file. The top-level `SHA256SUMS` lists every delivered file except
itself.

- `logs/`: preflight, toolchain, cache store, roots, cache get and checks, and the cache probe.
- `build/`: the bootstrap, the sweep, the development checks and the aborted sweep. Each has `results.jsonl` and
  per-module logs.
- `axioms/`, `statements/`, `headers/{insertion,frozen,t4}/`, `clash/`, `overlap/`, `lint/`.
- `subagents/tools-agent/`.
- `tools/`: a copy of the checkpoint's `tools/`, with the shared-tree backup and restore tools removed. Adapted:
  `review/runner.py` and `seal/runner_full.py` (headers state the changes). New: `drivers/rule10_final.sh`,
  `seal/review/mkctl_bb1m_readers.py`, `deliver.py`, `sweepsum.py`, `t4_header.py`, `widths.py`.
- `delivery/`: the `git am` reproduction check.
