# GSW 6b U18+U19 `gsw-6b-u18-u19` · final r1 · phase 2: replay on olean snapshot #11

**Verdict: PASS, with no new finding.** The delivered head `4672ed30` was replayed on its own copy of snapshot #11 (B6 +
the unit), then **stacked on the records tip** (with U12/U13) on a second copy. Both build with the root `TCSlib`;
`PolyRatio.olean` and `Asymptotic.olean` are byte-identical in the two trees. The full 6b stack (records tip + U14+U16
+ U15+U17 + U18+U19), replayed once for both units of this review, makes all five targets standard-only.

- **Build.**
  - **B6 + U18+U19:** 6/6 modules rc 0, including the root `TCSlib`; 0 `error:`/`error(`, the substring "error" 0
    times; **0 warnings** (no `sorry` warning anywhere in the rebuilt modules).
  - **Stacked on the records tip:** 12/12 rc 0, 0 errors; the 10 `sorry` warnings are other units' targets (Bootstrap
    5, Circular 1, Leveled 2, LeveledSecurity 2).
  - **Checks.** No `audits/*/Checks` imports a changed module; both pass the state check.
- **Admissions:** **37 in 14** on B6 (`base-sorries.txt` minus the five targets: the brief's C2 count); 28 in 12 stacked.
- **Axioms.** 37 stored constants: 32 standard, 5 reaching `sorryAx` only through allowed frozen targets of U14-U16
  and U15-U17; **A1 and the helper standard-only**; the same names and sets as the worker's census. Identical stacked.
  In the full 6b stack: 0 `sorryAx`.
- **Seals.** Canonical coe-A and seal B: rc 0, 0 errors; PolyRatio 1,394 (A) / 1,395 (B), Asymptotic 1,653 / 1,654,
  requested and verified. **Own-definition seal** of `PolyRatio.lean` (`ofFamily`, `pBoot` irreducible): compiles,
  NEG control fails once.
- **Controls.** 4 liveness pairs (the helper's included), ALL_OK. **Unfold scan:** 0 definitions.
- **Duplication probes.** At B6: E1–E6 no lemma, the control K3 found; at the head E1 finds the helper (control).
- **Lint.** Unchanged. **Snapshot #11:** 0/0/0 before, mid-run and at the end.

Run on 2026-11-19 from 01:36 to 02:21 UTC (U15+U17 first, this unit 02:01–02:15, then the full stack). `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`; the work directory is
`$SP/g6b-u1517-1819/`. Lean processes, disk, what was not done and not touched: as in `U15-U17/final-r1/phase2.md`
(one at a time; 77 starts plus 2 `mathlibextra` for both units; never more than 2 other Lean processes at a start; no
waits; lowest free disk 6,315 MB; no `lake build`, cache get, commit on a ref, push or PR).

## P2-0 Inputs

As for U15+U17: records tip `c87eb403` (later `a25338e0`), `TCSlib` tree `745bf4b4`; snapshot #11 map `e7bb03b4…`
verified 0/0/0 before the first copy; recipe tools unmodified. **Delivery:** exchange `4da71016…`, final `c414248e3`;
both manifests pass (484 and 477 rows).

## P2-1 Heads (scratch only)

- **Reproduction.** The 2 patches on B6 give `479f6a88…`, `4672ed30…`, as delivered (`logs/repro-u1819.log`).
- **Stacked head.** `git merge-tree --write-tree 4672ed30 c87eb403` is clean, tree `7658b9ea…`, `TCSlib` tree
  **`6cfe46bf55c7fa25387de44fd20474f01b6c91d0`** (the same against `a25338e0`); committed on no ref as
  **`0656a95a024c10107a067b680fc6b50c7ef4bdf4`** (`logs/stack-head-u1819.txt`).

## P2-2 B6 + U18+U19

- **Copy and overlay.** `cp -al` copy, 3,346 Mathlib symlinks, `NthRootLemmas` (`c0a9cff0…`) hard-linked from the
  U15+U17 B6 tree.
- **Plan.** `downorder.py` at `4672ed30`: **changed 2, down 6** (the two owned files, `GSW`, `Homomorphic`,
  `AdvancedEncryption`, the root); **6 to build, 1,450 to reuse**.
- **Build** 02:03:35–02:03:53. **6/6 rc 0**, 2.0–4.8 s per module, peak maxrss 4.58 GB (the root). Every log is empty
  of errors and warnings.
- **Accept.** `permod.py`: 6 modules, 0 bad. `stateplan update`: 6 taken. `check`: **1,456/1,456 RESULT OK**, again at
  the end. Link count 1: exactly the 6 rebuilt oleans.
- **Admissions:** **37 in 14**; removed exactly G16, both G17, A1, A3; none added.

## P2-3 Stacked on the records tip

- **Plan** at `0656a95a`: changed 4, down 12; **12 to build, 1,444 to reuse**.
- **Build** 02:13:11–02:13:42: **12/12 rc 0**, 0 errors; the 10 `sorry` warnings are U14+U16's 7 and U15+U17's 3.
- **Accept.** `check` **1,456 RESULT OK** (and at the end); link count 1 for the 12.
- **Admissions:** **28 in 12**.
- **Cross-tree:** `PolyRatio.olean` `1b1f1a83…` and `Asymptotic.olean` `71d20776…` equal P2-2's
  (`logs/olean-cross-u1819.txt`).

## P2-4 Axioms

`G6bProbe/u1819/Axioms` (census over `PolyRatio` and `Asymptotic`, `sorryAx` trace, the five targets and the helper by
name, a `sorry` control): rc 0, 11 s.

- **37 stored constants** (PolyRatio 11, Asymptotic 26): 12 `[Classical.choice, Quot.sound, propext]`, 11
  `[Quot.sound, propext]`, 9 `[propext]`, and 5 with `sorryAx`.
- **The five traces:** `bootRatio_le_poly` → `[bootNoise_le]`; the private glue → `[bootNoise_le]`;
  `decrypt_fheEval_of_ratio` → `[bootNoise_le, decrypt_keygen_fheEvalCircuit]`; `decrypt_leveledEval_of_ratio` →
  `[bootNoise_le, decrypt_keygen_leveledEvalCircuit]`; `leveledINDCPA_of_dlweAssumption` → `[distAdv_leveledView_le]`.
  Every name is an allowed frozen target of U14-U16 or U15-U17; none is in `PolyRatio.lean` or `Asymptotic.lean`.
- **Targets** (census and `#print axioms`): **A1 `[propext, Classical.choice, Quot.sound]`**, **the helper
  `[propext, Quot.sound]`**; G16, both G17 and A3 the three plus `sorryAx`.
- `logs/axcmp-u1819.txt`: the worker's census has the same 37 names with the same sets: RESULT SAME.
- **Control** `[sorryAx]`. **Stacked tree:** identical census (`runs/u1819-stack-axioms`).
- **Full 6b stack** (`runs/full-axioms`, U15+U17's P2-7): all five targets `[propext, Classical.choice, Quot.sound]`,
  the helper `[propext, Quot.sound]`, 0 `sorryAx` over the four owner modules of both units.

## P2-5 Rule 10

- **Collector:** rc 0, 2,295 CAT rows; `PolyRatio: stored 11`, `Asymptotic: stored 26`.
- **Canonical coe-A:** PolyRatio **1,394 requests** (30 term names, 17 excluded: abbreviations and `PolyExpr.eval`),
  Asymptotic **1,653** (44 term names, 23 excluded). **rc 0, 0 errors**: `requested=1394 active=1376
  already_irreducible=18 verified=1394` and `requested=1653 active=1634 already_irreducible=19 verified=1653`, each with
  its `G06-SEAL-END`.
- **Seal B** (`SEAL_EVAL=1`, `PolyExpr.eval` sealed too): 1,395 and 1,654 requests, **rc 0, 0 errors**, verified =
  requested. `Parameters.ofFamily` and `pBoot` are among Asymptotic's requests (foreign there).
- **The worker's counts agree:** coe-A 1,394 / 1,653, coe-B 1,395 / 1,654.
- **Own-definition seal** (`runs/u1819-ownseal`, source `probe-src/u1819/OwnSeal_PolyRatio.lean`). In `PolyRatio.lean`
  `ofFamily` and `pBoot` are the file's own, so the canonical seal leaves them open. The probe is the head source with
  `attribute [irreducible] Parameters.ofFamily pBoot` inserted right after `pBoot_eq`, followed by a NEG/POS pair at the
  end. It gives **exactly 1 error, at the NEG line** (249: `(ofFamily F κ).lwe = F.parameters κ` by `rfl`); the helper,
  G16, the glue and both G17 compile with both definitions sealed. So no proof of this unit reads `ofFamily`'s body,
  even in its own file (type-level Rule 10, Gate 46).
- **Liveness pairs** (`mkctl2.py`):

  | Owner | Pair | Sealed | Open |
  |---|---|---|---|
  | PolyRatio | `GSW.bootNoise` / `bootNoise_eq` (Bootstrap) | NEG 429: 1 error; POS 430 passes | 0 errors |
  | PolyRatio | `GSW.decDepth` / `decDepth_eq` (DecryptFormula) | NEG 433: 1 error; POS 434 passes | 0 errors |
  | Asymptotic | `LWE.decisionAdvantage` / `decisionAdvantage_eq` | NEG 642: 1 error; POS 643 passes | 0 errors |
  | Asymptotic | **the helper's pair:** NEG `(ofFamily F κ).lwe = F.parameters κ` by `rfl`; POS `Parameters.ofFamily_columns_le F κ` used with `ofFamily` sealed | NEG 646: 1 error; POS 647 passes | 0 errors |

  **ALL_OK** (`logs/controls-check-u1819.txt`).
- **Explicit-unfold scan:** 66 identifiers over both files, **0** resolving to a TCSlib definition (all theorems, plus
  the local `hw`).

## P2-6 Duplication probes

`G6bProbe/u1819/DupProbe` (`exact?`, 400k heartbeats; the use's hypotheses and instances, G53-01), run **at B6** on a
tree whose `PolyRatio`/`Asymptotic` oleans are B6's (`runs/u1819-dup-b6`) and **at the head** (`runs/u1819-dup-head`):

| Probe | At B6 | At the head |
|---|---|---|
| E1 the helper's statement (`F : LWE.Family`, `κ`) | fails: no lemma | `exact Parameters.ofFamily_columns_le F κ` (control) |
| E2 `Nat.clog 2 n ≤ n` | fails | fails |
| E3 `β ≤ bootNoise P β` | fails | fails |
| E4 `8·y < q → 2 ≤ q → 2·y < q/2` | fails | fails |
| E5 `0 ≤ distAdv X Y D` (`Fintype` σ τ ρ) | fails | fails |
| E6 `0 ≤ LWE.decisionAdvantage P χ D` (`Fintype`, `Nonempty` ρ) | fails | fails |
| K3 `n < 2 ^ n` (control) | `Nat.lt_two_pow_self` | `Nat.lt_two_pow_self` |

rc 1 by design (6 and 5 errors). Name searches: `logs/searches-u1819.txt`.

## P2-7 Full 6b stack

See `U15-U17/final-r1/phase2.md`, P2-7: head `6e363a29…`, `TCSlib` tree `37ae0f32…`, 12/12 rc 0, 0 `sorry`
warnings, admissions 18 in 8, 0 `sorryAx` in the four owner modules.

## P2-8 Lint

`campaign_style_lint.py --check8b`: **92 FAIL / 103 WARN over 540 files** at B6, at `4672ed30` and at `0656a95a`;
identical FAIL/WARN line sets (only the two size INFO lines change). `style_lint.py` on the owned files: **0 findings**.

## P2-9 State after the run

- **Deleted:** `olean-replay-u1819-b6` and `-u1819-stack` (02:14Z), after `check-end` (1,456 OK each) and a re-hash of
  the rebuilt oleans (unchanged); the full-stack tree at 02:21Z.
- **Snapshot #11:** `snapmap.py verify` **0/0/0** at the end (02:21Z).
- **Scratch commits** (on no ref): `479f6a88`, `4672ed30`, `0656a95a`, and the full-stack chain.

## What this changes in `review.md`

| Item | Phase 1 | After phase 2 |
|---|---|---|
| C1/C2 build and admissions | worker's sweep (5 modules, root not built) | **reproduced**, with the root, on B6 and stacked; 37 in 14 |
| C5 axioms | worker's census and traces | **reproduced**: 37/37, same sets, traces only through allowed names; A1 and the helper standard |
| C6 Rule 10 | worker's seals | **canonical coe-A and B** pass; own-definition seal of `ofFamily`/`pBoot`; 4 pairs; unfold scan 0 |
| Duplication | static | E1–E6 no lemma at B6 (E1 found at the head) |
| New findings | U1819-F01–F03 | none |
