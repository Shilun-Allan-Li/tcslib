# Fill `pair-bdh`: T1 `bdhAssumption_of_dbdhAssumption` (Decision BDH implies BDH)

In-house fill job, 2026-11-16 UTC, under the overnight authorization (Codex audits later). `$SP` =
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`. Paths below are relative to this
directory unless they start with `$SP`.

Rules followed: `python3 -I` throughout; `PATH=$HOME/.elan/bin:$PATH`; Lean 4.25.0; no `lake` command and no cache get;
Lean ran only through `scripts/lean_check_tree.sh` (build, `tools-used/review/runner.py`), through LE-gate40's
`runner_full.py` (`lean -DmaxErrors=0 <probe>`, no `-o`), and through `tools-used/devcheck.sh` (development only, no
`-o`). Only `$SP/dl-oleans` was used (exclusive to this job); `dl-oleans-2` was not touched; one Lean process of this job at
a time; no process was killed. `/home/user/tcslib` was only read (git object reads; `git worktree add` created the
worktree and branch). Nothing pushed.

## Commit

- Worktree `$SP/wt-fill-pair-bdh` (sparse: `TCSlib/`, `audits/`, `scripts/`, lake files, `lean-toolchain`, `policy.md`,
  `TCSlib.lean`; `.lake/packages` symlinked), local branch `fill/pair-bdh` from `9e7a96481785d6cac4dea3b2e990c49ac278b060`
  (#331 head).
- `916afc25c21f5e52b4b01958186ad55d2f615fd1` "pair-bdh: prove BDH from DBDH (T1)", signed by the default signing
  (`gpgsig` SSH header present; local verification is not possible here: no `ssh-keygen`, and the configured signer
  only signs). Trailers as instructed. `git/` (commit object, diff, diffstat, checks).
- Diff: `TCSlib/Cryptography/Pairing/Assumptions.lean` only, +227/−8 (221 → 440 lines).

## What changed

- T1 header byte-identical; its body (`sorry`) replaced (8 lines); its `**Proof sketch.**` rewritten to the delivered
  proof. Statement prose and the Source paragraph unchanged.
- Four imports added: `Complexity.Randomized.Closure` (layout readers), `Complexity.Randomized.Repetition`
  (`polyTimeComputable_pairEq`), `Cryptography.Games.Bridges.Experiments` (`prob_sample_eq_uprob`),
  `Cryptography.OneWayFunctions.Basic` (`uprob_congr`, `uprob_eq_one_div_card`). All were already in the 109-module
  pairing closure except `Bridges/Experiments` (closure now 110).
- Ten `private` declarations, each with a docstring stating its formula; the two with proofs of 15 lines or more
  (`exists_bdhDistinguisher`, `accept_bdhGame_le`) carry a `**Proof sketch.**`:
  `tupleBdh`, `tupleTgt` (string projections of a Decision BDH string), `tupleBdh_tupleStr`, `tupleTgt_tupleStr`,
  `polyTimeComputable_tupleBdh`, `polyTimeComputable_tupleTgt`, `exists_bdhDistinguisher` (the machine),
  `distinguisherL_tupleStr` (its verdict on a tuple string), `prob_eq_encT_le` (`Pr_t[w = enc t] ≤ 1/p`),
  `BilinearGen.accept_bdhGame_le` (`Pr[A wins] ≤ dbdhAdv D κ + 2^{-κ} + δ(κ)`). No public declaration added, no
  `@[simp]`, no `sorry`, no `native_decide`; widths ≤ 100 characters.

**Route** (Gate 40's): `D` re-pairs the first five components of the input into the BDH string, runs `A` with its own
coins and outputs `[true]` iff the answer equals the last component. `D := NUPPT.ofPolyTime` of the raw layout
function with `A`'s coins and advice. On `P_BDH` acceptance equals `A`'s success (coins moved by `coinsCongr`,
`expect_sample_equiv`; the unused `T` sample by `expect_const`); on `R_BDH` the samples of `T` and the coins are
exchanged (`expect_sample_comm`) and injectivity of `encT` gives `≤ 1/p`; `1/p ≤ 2^{-κ} + [p < 2^κ]` and the bad coins
cost `≤ δ(κ)` (`orderAtLeastExcept_iff`, `prob_sample_eq_uprob`). No group operation, decoding or `Ops`.

## Checks

| Check | Result | Evidence |
|---|---|---|
| Statements | `decls2.py` vs `9e7a9648`: no public declaration added, removed or changed. `touched.py`: T1 CHANGED, 10 private ADDED, all others UNCHANGED | `statements/` |
| Frozen header | `frozen_check.py`: reverting only the 4 imports, the 2 private helper blocks, T1's sketch paragraph and body gives the base file byte for byte: PASS. Controls (T1 header, T1 prose, another docstring, another proof, a public helper, a fifth import): 6/6 FAIL as required | `frozen/` |
| Build (`lean_check_tree.sh`) | closure of the 10 owners + `Pairing` + `KeyExchange` at `916afc25`: 110 modules; 36 built (16 snapshot oleans overwritten, 20 new), 74 reused by closure key (69 snapshot at `eff2dcd0`, 5 dev-built from `9e7a9648` sources, identical at the head). 36/36 rc 0, `error:` 0, `error(` 0 (also the 5 dev-built: 5/5 rc 0, 0/0). State check over the 110: RESULT OK. Sources bound to `git show` (41/41) | `build/per-module.tsv`, `dev-build/`, `state/statecheck.txt`, `checks/source-binding.txt` |
| Downstream | `Assumptions` and every pairing module downstream of it (`Joux`, `KeyExchange`, `BonehBoyenMachine`, `BonehBoyenSecurity`, `IdentityBased`, `AdvancedEncryption`, `Pairing`) rc 0, 0/0 errors; their oleans are byte-equal to gate40-seals-merged's build of `9e7a9648` (40 of 41 equal; only `Assumptions` differs) | `checks/olean-vs-g40m.txt` |
| Admissions | `sorry` warnings 39 → 38 over the same 41 modules (only `Assumptions` 1 → 0); source census: T1's `sorry` removed, none added; T2–T4 remain | `admissions/` |
| Axioms | `#print axioms bdhAssumption_of_dbdhAssumption`: `[propext, Classical.choice, Quot.sound]`. LE-gate40 census probe (verbatim) on the head: 397 constants; vs seals-merged: T1 loses `sorryAx`; added the 12 private constants (incl. `tupleBdh.eq_1`, `tupleTgt.eq_1`) and the realized `Complexity.NUPPT.coinsCongr.congr_simp`, all standard; `sorryAx` only in T2–T4 and `bb1_sidSecure` | `axioms/` |
| Rule 10 seals | changed owner `Pairing/Assumptions`, LE-gate40 tools verbatim (`rule10_b.sh`): strict A/B, coe A/B (coe A canonical) 4/4 rc 0, `error:`/`error(` 0, install + EOF records, no failing declaration; requests 895/896/894/895; 49 term names, 28 in the closure (sealed), 21 excluded (abbrevs/projections, `PolyExpr.eval` notation) | `rule10/seals-*.tsv`, `rule10/seal-runs/`, `rule10/seals*/` |
| Paired controls | `mkctl_pbdh.py` = `mkctl_g40.py` + 9 rows (`distinguisherL`, `runAtL`, `layout`, `ofPolyTime`, `advInput`, `accept`, `uprob`, `OrderAtLeastExcept`, `inst`): strict and coe ALL_OK True; sealed negatives 12 (A) and 13 (B, with `PolyExpr.eval`) per harness each fail exactly once; readers pass; unsealed all pass. Unsealed pretest of the rows: `rule10/pretest/` | `rule10/ctlcheck-*.log`, `rule10/controls-*` |
| Explicit-unfold scan | 69 items: THEOREM 60, OWNED_DEFINITION 4 (`rw`/`unfold` of the file's own `tupleBdh`, `tupleTgt`), LOCAL_OR_UNRESOLVED 3 (`hD`, `h`, field `B.card_GT`), SIMPROC 2 (`reduceIte`); 0 foreign | `scan/` |
| Lint | `campaign_style_lint.py TCSlib/Cryptography --check8b`: base and head both 92 FAIL / 103 WARN over 396 files; non-INFO line sets identical (only `Assumptions`' INFO line changes). `style_lint.py` on the file: 0 findings | `lint/` |
| Tree | restored: 20 backups put back (0 hash failures), 21 new oleans deleted; snapshot-post = snapshot-pre = `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` (SNAPSHOT EQUAL), restoreplan extra 0 / changed 0 / missing 0, second snapshot equal | `tree/`, `restore/` |

Development runs (not evidence, nothing written to the tree): `devcheck.sh` on the draft `Assumptions.lean` (rc 0,
first attempt), a scratch copy with `#print axioms` (standard), the control-row pretest, and two probes on the realized
`coinsCongr.congr_simp` (`checks/congr/`: it originates in `Assumptions`; `CollectionsHelpers` does not have it).

## Overlap and reuse

No published lemma is duplicated: every new declaration is `private`, specific to the tuple format of this file, and
no TCSlib file proves Decision BDH ⇒ BDH or decisional ⇒ computational Diffie–Hellman (searches: `overlap/search.log`).
Disclosed overlaps of pattern or near-alternatives:

1. **The machine** (`exists_bdhDistinguisher`) is built as `NUPPT.ofPolyTime` of a raw layout function, the documented
   pattern of `exists_comp`'s docstring and of `EnsemblesLemmas.exists_pushRed`, `NextBit.exists_nextBitDistMachine`
   (private) and many reductions (68 files use `ofPolyTime`). The published one-call wrapper `NUPPT.wrap`
   (`Asymptotic/ReductionSupport.lean`) could also express it (post-processing sees the view and the answer); it was
   not used because its coins are `0 + A.coins` and its advice `⟨[], A.advice⟩`, which would add a coin-equivalence
   detour, while the raw function keeps `A`'s coins (published `coinsCongr`). `exists_compParam`/`exists_comp` do not
   fit (their post-processing does not see the argument). No new combinator was introduced.
2. **The equality test** reuses `polyTimeComputable_pairEq`; the private one-line helpers of the same kind elsewhere
   (`DiscreteLogHardcore.dlb_eq_poly`) were not copied.
3. **Projections**: `tupleBdh`/`tupleTgt` are compositions of `pairFstD`/`pairSndD` with `polyTimeComputable_pairFstD`,
   `polyTimeComputable_pairSndD`, `PolyTimeComputable.pairEncode`, `PolyTimeComputable.comp'`. There is a published
   `polyTimeComputable_iterate_pairFstD` but no iterated-`pairSndD` polynomial-time lemma; the five-fold composition is
   written out (four `comp'`).
4. **`prob_eq_encT_le`** is assembled from published lemmas (`Games.Bridge.prob_sample_eq_uprob`,
   `OneWay.uprob_congr`, `OneWay.uprob_eq_one_div_card`, `uprob_false`). Near alternative: `ProbComp.expect_sample_mem_le`
   (`Games/Hopping.lean`, `𝔼[t ∈ L] ≤ |L|/|T|`) with `L` the at-most-one preimage; not a duplicate.
5. **The verdict identity** `decide ([decide P] = [true]) = decide P` is done inline with core `simp` lemmas
   (`List.cons.injEq`, `and_true`, `decide_eq_true_eq`). The same identity is the published
   `decide_singleton_eq_true` (`Encryption/PublicKey/TrapdoorPredictor.lean`); not imported (it would bring the
   public-key layer into the pairing closure); no lemma copied.
6. **The order bound** (`hord` in `accept_bdhGame_le`: `E_r[1/p] ≤ 2^{-κ} + δ(κ)` by a pointwise bound with a bad-coin
   indicator) follows the same pattern as ElGamal's private `dlc_uprob_bad_le` (`uprob` layer, safe primes); there is
   no published Games-layer lemma for it.
7. **The final inequality** `accept(real) ≤ accept(random) + advantage` is inline (`advantage_eq`, `abs_sub_comm`,
   `le_abs_self`); `Games/Advantage.lean` has no such lemma.

No duplicated proved material; nothing for the duplication ledger.

## Limits

- Seals cover the changed owner only (as instructed). The downstream owners' sources are unchanged and their oleans
  equal the `9e7a9648` build, but `Assumptions`' import closure grew from 33 to 58 modules (`work/asm-closure-*.txt`;
  the 25 added are all in the 110-module pairing closure), so their request sets may grow; their seals were not re-run here.
- Root `TCSlib` not built (as in LE-gate40 and the seals-merged supplement).
- The commit's SSH signature could not be verified locally (see Commit).

## Tools (`tools-used/`)

Copied unmodified: `fullorder.py`, `stateplan.py`, `restoreplan.py`, `permod.py`, `restore_derand.sh`, `snapshot.py`,
`review/runner.py`, `backup_g40m.py` (gate40-seals-merged's `tools-used/`), and `seal/` = LE-gate40's `tools/` verbatim.
New here: `backup_cum.py` (cumulative form of `backup_g40m.py`, which was copied but not run), `devcheck.sh`, `frozen_check.py`,
`frozen_controls.py`, `seal/review/mkctl_pbdh.py` (header states the change). Drivers: `run-build.sh`,
`rule10_pbdh.sh`, `finish-restore.sh`. `work/`: the development closure and its plan. `state/state-init.json` (init at
`eff2dcd0` from the snapshot) is byte-equal to gate40-seals-merged's.

`SHA256SUMS` lists every file here except itself.
