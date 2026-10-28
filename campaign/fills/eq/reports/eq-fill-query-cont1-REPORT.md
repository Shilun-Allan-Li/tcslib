# E-Q cont1 — `exists_queryTM`'s main machine: fill report (complete)

**Status: complete — the target is proved; all seven checkpoints reached.** The setup of the
main machine `M₁` is proved as a run of its phase host, with its `O(n)` bound, in both branches
(`n ≥ 3` and `n ≤ 2`); one round of the locator is proved as a `Turing.Round` at its anchor with
its three escapes (interior, top, timeout) and its cost; the locator's loop is proved: from the
first rung to an escape at the stage `stage f n`, with the top flag, within `qyLoopA κ (n + 1)`;
both writers are proved: from the locator's escape each halts with the query's word as its
output, within its bound; and `M₁` is assembled: `hmain` is `qy_main`, so `exists_queryTM`'s
body is `exact qy_main hf hg` after the landed `suffices`. The owned file keeps exactly one
sorry, `exists_diagonalizer`'s (out of scope). This is the final delivery
(`fill-eq-query-cont1.zip`). After checkpoint 7 two finishing commits followed: the semantic
duplication search's citation (`QyKit.tape_cases` now cites `Classical.exists_or_forall_not`)
with four unused privates dropped (`323e3588`), and the after screen's two in-file copies
factored (`e952bc50`). Every check below is on `e952bc50`.

| item | value |
|---|---|
| brief | `eq-fill-query-cont1.md`, SHA-256 `e44de76f9b0f7657219503b790a8f045cf0d97fb3e901fd11bb59d07e0a47ca4` (verified) |
| addendum | `fill-environment-addendum.md` v2.6, SHA-256 `9f5bd5e74bb767e50a6e7a372e98a5567998ec14be432c1dfb7ff8856eb9bd28` (verified) |
| base | `43fe918f2b7612b46d6b1bd6d4201651f7243430` on `complexity/arora-barak-ch3-4` |
| owned file's blob at base | `f965eac02e06549e8239c7476b31c0ced4f3d11b` (expected value; verified) |
| branch / checkpoint commits | `fill/eq-query-cont1`: cp2 `21dd053c`, cp3 `68a5d3f0`, cp4 `12d94cdc`, cp5 `a1db58c7`, cp6 `258e3f1b`, cp7 `ce0c8aca`; finishing `323e3588`, `e952bc50` (final) |
| ancestor check | `git merge-base --is-ancestor 43fe918f HEAD`: yes (rechecked at `e952bc50`); the base was an ancestor of `origin/complexity/arora-barak-ch3-4` at `a63188dd` when checked (`logs/inputs-check.log`; the branch has since moved to `3b1814bc`, fetched only at depth 1 for the duplication search); no rebase, merge or cherry-pick |
| brief copy | the repository copy equals the attachment except its 4 `@ANCESTOR@` placeholders (4 lines; `logs/inputs-check.log`) |

## The zip's contents

- `REPORT.md`; `source/TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean` (the full
  modified source at `e952bc50`); `patches/` (`git format-patch 43fe918f..HEAD`: one patch per
  checkpoint commit and the two finishing commits); `fill-eq-query-cont1.bundle` (`git bundle` of
  `fill/eq-query-cont1` whose only prerequisite is the base; `checks/bundle-verify.txt`).
- `logs/`: the environment logs (preflight, toolchain, cache store, roots, cache fetch, manifest
  check, zero-olean scan, cache probe, inputs check), the bootstrap log with each module's time
  and maximum memory, the bootstrap's sorries by name.
- `checks/`: `final-sweep.log` (the 84 modules, each module's time and maximum memory),
  `tail-check.log`, `axiom-log.txt` (with `QyAxioms.lean`, the scratch copy with the prints),
  `walk.out` (the elaborated-constant walk and the public names), `inspection-table.md`,
  `lint.log`, `rule11-grep.txt`, `decls.md` (every new declaration with its docstring's first
  sentence), `bundle-verify.txt`, `head.txt`.
- `seal/`: `QySealed.lean` (the sealed copy), `QySealControls.lean` (the controls),
  `sealed-names.txt`, `walk_tail.lean`, and both raw outputs `sealed.out` and `controls.out`
  (each with its command and exit status).
- `probe/`: `QyImportProbe.lean` (the extended import probe) and `probe.out`.
- `screens/`: both screen outputs (`screen-before.txt`, `screen-after.txt`) with their start,
  end and exit records.
- `dup/`: the semantic search (names, hits, statement patterns and hits, the `exact?` probe's
  source, output, map and results, the per-private table).
- `runtime/`: the scripts that produced all of the above.

## Environment (addendum Part 1)

Logs in `logs/` (copied from `evidence/logs/` at the clone's root).

- **Preflight** (`preflight.log`): 4 CPUs; cgroup v1 memory limit 14,341,890,048 bytes
  (13.36 GiB), fail count 0, no OOM kill; clone free space 24.44 GiB before the toolchain
  (floor 12 GiB), 22.03 GiB after (floor 8 GiB).
- **Toolchain** (`toolchain-install.log`): `leanprover/lean4:v4.25.0` (commit `cdd38ac5`).
- **Cache store before the first fetch** (`cache-store.log`): `/root/.cache/mathlib` absent
  (0 files, 0 bytes).
- **Roots** (`mathlib-roots.txt`): the 34 Mathlib roots the order list's modules import directly.
- **Cache fetch** (`cache-get.log`): the filtered `lake exe cache get` for the 34 roots only:
  1003 files downloaded and unpacked, "Completed successfully!", 1 m 27.8 s. Never `lake build`,
  never the unfiltered fetch.
- **Manifest check** (`manifest-check.log`): 11 packages present, all match the manifest; 4
  absent (not cloned: `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`): PASS. Zero-olean
  scan empty (`zero-oleans.log`); cache probe OK (`cache-probe.log`, 2.3 s).
- **Bootstrap** (`bootstrap.log`): the 84 modules of the order list, one at a time through
  `scripts/lean_check_tree.sh`, 20:51:37–21:07:59 UTC (16 m 22 s; summed module wall time
  978.7 s; maximum resident memory 3.03 GB), each module's start, end, wall time and maximum RSS
  logged. **Sorry warnings: 20 in 9 modules, by name exactly the base list**
  (`bootstrap-sorries-by-name.txt` against `eq-fill-query-cont1-base-sorries.txt`).
- **Before screen** (`screens/screen-before.txt`), right after branching, under `nice -n 10` on a
  frozen worktree: 1,781 declarations, 2,165 pairs, 758,766 characters — equal to the screen
  base. 20:51:47–21:18:31 UTC, exit 0.
- **One Lean process at a time** throughout: every check, probe, seal and sweep ran
  sequentially (the screen ran beside the bootstrap, as the brief allows).

## Base sorry list (by name)

`branchTM_spaceUsed`; `idTM_computes`, `ifEqTM_computes`, `condTM_computes_iff`;
`pairDiagTM_computes`; `FinTM.lengthBitsTM_computes`, `FinTM.lengthBitsTM_spaceUsed`;
`timedCondTM_computes`, `timedCondTM_spaceUsed`; `loopHostTM_contracts`, `loopHostTM_decides`,
`loopHostTM_finds`, `loopHostTM_spaceUsed_le_budget`, `emitLoopTM_computes`;
`polyUnaryTM_spaceUsed`, `unaryTokenTM_computes`, `appendBitTM_computes`;
`exists_codeNDTM_accepts_linear`; `exists_queryTM`, `exists_diagonalizer`. None touched.

## Checkpoints reached

| checkpoint | state | commit | zip |
|---|---|---|---|
| 1 the guard | landed at the base | — | — |
| 2 the setup | **proved** | `21dd053c` | `fill-eq-query-cont1-cp2.zip` |
| 3 one round | **proved** | `68a5d3f0` | `fill-eq-query-cont1-cp3.zip` |
| 4 the loop and its ledger | **proved** | `12d94cdc` | `fill-eq-query-cont1-cp4.zip` |
| 5 the seek and the stage code | **proved** | `a1db58c7` | `fill-eq-query-cont1-cp5.zip` |
| 6 the budget field and the writer | **proved** | `258e3f1b` | `fill-eq-query-cont1-cp6.zip` |
| 7 `M₁` and the target | **proved** | `ce0c8aca` | `fill-eq-query-cont1-cp7.zip` |

**Open declarations.** None of the fill's: the target is proved. `exists_diagonalizer` (E-D)
is out of scope and untouched. No new declaration contains a `sorry`.

**The axiom prints** (`axiom-log.txt`, at `e952bc50`): `exists_queryTM` depends on
`[propext, Classical.choice, Quot.sound]`, and every one of the 211 new privates prints within
`[propext, Classical.choice, Quot.sound]` (212 prints in all, no `sorryAx`).

## What checkpoint 2 proves

`qy_setup_long` (`n ≥ 3`): from the blank start `qyC ⟨s1, inl ()⟩ 1 (fun _ => bufferTape [])
(fun _ => 0) []`, the setup host `qySet κ` runs, within `qySetB κ n = (cbA + prA +
2 |bits D₀| + 60) (n + 1)` steps and avoiding its three exits `qySetF κ` before the end, to its
exit `⟨s10, done⟩` on the layout `qyLay κ n 3 0 0` with every head at `0` and the input head at
`1`. `qy_setup_short` (`n ≤ 2`): within the same bound, to the test's verdict `⟨s6, done v⟩`,
`v ∈ {lt, eq}` (where `M₁` dispatches to its halting phase, which outputs `[]`). `qy_setup_head`
is their common prefix up to the test.

The setup's phases (`QySK`, `qySetM`, `qySetRed`): `s1` the input call of `bits |x|` (`cb`,
released, embedded on bank `bCb`, tape `0` on the width tape `1`); `s2` the expansion of `bits n`
onto tape `0` (giving `1^n`, and the counter becomes `1^{|bits n|}`); `s3`/`s4` one more cell and
the rewind (`1^{n+1}`); `s5` the first rung `1^3` (`a₀ = ℓ₀ + 1`, `ℓ₀ = 2`); `s6` the test
`n + 1` against `3` (L2, `qyCmpTM`): `gt` iff `n ≥ 3`; `s7` the seek's tape `[true]`; `s8` the
width word copied to tape `9`; `s9` the install call prepending `1^{|bits D₀|}` (`pr`), giving
the all-ones counter `1^m`, `m = |bits D₀| + |bits n|`; `s10` its copy onto the clock's tape `8`.
Every phase is `O(n)`.

## What checkpoint 3 proves

`qy_round` (one round of the locator `qyLoc κ`, the phase host of `qyLocM κ` with dispatch table
`qyLocRed κ`): from the anchor `qyAnc κ = ⟨anc, sweep⟩` on the layout `qyLay κ n a j k` (rung
`1^a`, `a ≤ n`; `(j, k) = unpair h`), all heads at `0`, the input head at `1`, the run is a
`Turing.Round` with anchor `qyAnc κ` and escape set `qyLocE κ` (every state of the phases
`escI`, `escTop`, `escTO`). With `X = f a + a + 1` and `ℓ' = 2 ^ X⁴` (`= ladder f (h + 1)` when
`a = ladder f h + 1`, `qy_ladder_succ_eq`):
- **next** (`ℓ' < n`): back at the anchor on `qyLay κ n (ℓ' + 1) (unpair (h + 1)).1
  (unpair (h + 1)).2`, within `qyRndP κ n ℓ' j k = 11 ℓ' + 50 |bits n| + 4 m +
  5 cfA ((cfc + 3)(|bits n| + 1)) + puA |bits n|⁵ + abA (|bits n| + 1) + abA (j + k + 2) +
  6 (j + k) + 150`;
- **interior** (`n < ℓ'`): at `⟨escI, sweep⟩` or `⟨escTO, sweep⟩`, the tapes off the round's
  scratch (the clock's bank and tapes `3`–`6`) equal to the layout with their heads at `0`
  (`QyEscT`), within `qyRndS κ n a = 6 a + 5 · 2^m + 2 m + 40 (n + 1) + 16 |bits n| +
  puA |bits n|⁵ + abA (|bits n| + 1) + 70`;
- **top** (`ℓ' = n`): at `⟨escTop, sweep⟩`, input head `1`, `QyEscT`, and `1^{X - 1}` on tape
  `4` with its head at `0` (the budget's argument), within `qyRndS κ n a`.

It is assembled from the anchor's dispatch and four segments against the round's stop set
(`qy_round_of_seg`):
- `qy_rnd_call` — `r1` copies the rung onto `f`'s call tape; `clk` runs `C_f`, released at its
  entry, under the clock (`qy_clockHost_finish`/`qy_clockHost_timeout`, split on the call's time
  against `2^m − 1`). Timeout: `n < f a` (`qy_timeout_cert`), the timeout escape, every tape off
  the clock's bank untouched (`qy_clockHost_timeout`'s `unselected` clause), the output still
  empty (the timed-out call is silent).
- `qy_rnd_tests` — `r3` `|bits (f a)|` against `|bits n|` (L2; `gt` gives `f a > n`); `r4`–`r6`
  `1^{f a}` by `expandTM` on `bits (f a)` (`qy_expandHost`, cost `≤ 6 f a + 2 |bits (f a)| + 2`,
  and `f a ≤ 2n` here), `1^a` appended, rewind; `r7` `X − 1` against `|bits n|` (not shorter:
  `ℓ' ≥ 2^{|bits n|} > n`); `r8`/`pu` the fourth power `1^{X⁴}` by the install call; `r10` `X⁴`
  against `|bits n|`; `r11`/`ab` `0^{X⁴} 1` (worth `ℓ'`, `qy_rung_val`); `r13`–`r15` `1^{ℓ'+1}`
  (`ℓ' ≤ 2^{log₂ n} ≤ n` here); `r16` `ℓ' + 1` against `n + 1`: `lt` next, `eq` top, `gt`
  interior.
- `qy_rnd_clean` — `c1`–`c7`: clear the old rung, transfer the next rung, clear tapes `7`, `4`,
  `5`, `6`, restore the counter from its copy (`qy_copy_over`).
- `qy_rnd_pair` — `u1`, `incJ`, `u2`, `clrK`, `clrJ`, `incK`: `(j, k) ↦ unpair (h + 1)` by the
  successor rule of `Nat.unpair` (`qy_unpair_succ_lt`, `_last`, `_diag`, `_gt`, proved from
  `Nat.pair_eq_of_unpair_eq` and `Nat.unpair_pair`, `Nat.pair` reduced only in `show` steps).

## What checkpoint 4 proves

`qy_loop` (`n ≥ 3`): from `qyAt κ x 0` (the anchor on the layout of the first rung `ℓ₀ + 1 = 3`
and the pair `unpair 0 = (0, 0)`, which is the setup's long exit layout), the locator runs,
avoiding its escapes `qyLocE κ` before the end, to an escape at the stage `s = stage f n`:
- `n < ℓ_{s+1}`: the interior or the timeout escape;
- `n = ℓ_{s+1}`: the top escape, with `1^{f a + a}` (`a = ℓ_s + 1`) on tape `4`;

in both, the tapes off the round's scratch equal the anchor layout of the stage `s` (rung
`ℓ_s + 1`, pair `unpair s`) with their heads at `0` (`QyEscT`), within `qyLoopA κ (n + 1)` steps,
`qyLoopA κ = 22 + qyDk κ + 8 · 6⁶ · qyCk κ`. The passed rounds `i < s` are rounds from
`qyAt κ x i` to `qyAt κ x (i + 1)` (`qy_round`, `qy_ladder_succ_eq`; they pass since
`ℓ_{i+1} ≤ ℓ_s < n`, `stage_spec`); their times are chosen first (`choose`) and
`Turing.Round.iterate_seq` makes them one segment; the stopping round is appended by
`Turing.Round.segment` and `Turing.Segment.trans`.

**The ledger** (`hmain`'s locator term):
- the passed rounds: `∑_{i<s} (11 ℓ_{i+1} + qyCk κ (|bits n| + 1)⁵)` (`qy_rndP_le`, with
  `j + k ≤ i < s` by `Nat.unpair_add_le`) `≤ 22 ℓ_s + s · qyCk κ (|bits n| + 1)⁵`
  (`qy_ledger`) `≤ 22 n + qyCk κ (|bits n| + 1)⁶` (`s < log₂ n < |bits n|`, `qy_stage_lt_log`);
- the stopping round: `qyDk κ (n + 1) + qyCk κ (|bits n| + 1)⁵` (`qy_rndS_le`: `a ≤ n` and the
  clock's budget `2^m ≤ 2^{|bits D₀|}(2n + 1)`);
- the polylogarithmic terms: `(|bits n| + 1)⁶ ≤ 6⁶ · 2^{|bits n| + 1} ≤ 6⁶ · 4 (n + 1)`
  (`qy_pow6_le`: `x ≤ 6 · 2^{⌊x/6⌋}`; `qy_two_pow_bits_le`).

## What checkpoint 5 proves

After an escape (`QyEscT κ n a j k T P`, `j = (unpair s).1`):
- `qy_seek_run`: the input seek on tapes `12` (`[true]`, worth `1`) and `13` (blank), from any
  input head position, returns the input head to `1` within `rC (n + 4)` steps, every work tape
  and head unchanged (the kit's seek clause through `qy_seekHost`). It is needed after the
  timeout escape, where the input head is unknown; the middle writer runs it in every case.
- `qy_code_calls`: the increment's call on the bank of tape `10` (`1^j ↦ 1^{j+1}`, within
  `abA (j + 1)`), then the length call on the same tape (`1^{j+1} ↦ bits (j + 1)`, within
  `clA (j + 2)`); `stageCode s = (bits (j + 1)).dropLast` (`stageCode_eq`), the top bit dropped
  by the emitter.
- `qy_mid_code` / `qy_top_code`: the middle writer's phases `m0`–`m2` and the top writer's `t1`,
  `t2` as segments of their hosts, ending at the budget's call with `bits (j + 1)` on tape `10`.

The tapes the writers read are off the round's scratch: `qy_not_scratch_tp` (named tapes other
than `3`–`8`), `qy_not_scratch_ge` and `qy_bank_not_scratch` (the bank blocks past `f`'s call
bank), read through `QyEscT.tp` and `QyEscT.bank`.

## What checkpoint 6 proves

- `qy_mid_run`: from the middle writer's entry `⟨m0, rE⟩` on an escape's tapes (any input head),
  the middle writer halts within `qyMidB κ n j = rC (n + 4) + abA (j + 1) + clA (j + 2) +
  cgA (g n + 1) + 6 g n + 4 (j + 1) + 3 (n + 1) + 30` steps with the output
  `false :: pairEncode (pairEncode (bits (g n)) (bits (j + 1)).dropLast) 1^{n+1}`.
  Phases: the head (`qy_mid_code`); `m3` `M_g`'s input call from the blank seam on the bank of
  tape `14` (`exists_inputCallTM`, `O(g n + 1)`); `m4`–`m6` the emissions (L6).
- `qy_top_run`: from the top writer's entry on an escape's tapes with `1^{F + a}` on tape `4`,
  it halts within `qyTopB κ X a j = abA (j + 1) + clA (j + 2) + pbA X³ + 6 X² + 4 (j + 1) +
  3 a + 30` (`X = F + a + 1`) with the output
  `true :: pairEncode (pairEncode (bits (X²)) (bits (j + 1)).dropLast) 1^a`; `X² = budget f ℓ`
  for `a = ℓ + 1` (`budget_eq`). Phases: the head (`qy_top_code`); `t3` the square's install call
  on tape `4`; `t4`–`t6` the emissions.
- **L6, the emitter** (`qyEmitTM`, `qy_emit_run`, `qy_emit_stop`): a prefix, the tape's word
  (optionally without its last bit) with every bit written `rr + 1` times, a suffix; the third
  emission halts. **The writer's word** (`qy_writer_word`): the three emissions give
  `b :: pairEncode (pairEncode B W.dropLast) N` (`pairEncode_eq` twice; the doubled doubling is
  quadrupling, `qy_flatMap_dbl_dbl`), which is `query_eq`'s word with `B = bits (g n)` or
  `bits (budget f ℓ)` and `W.dropLast = stageCode s` (`stageCode_eq`).

## What checkpoint 7 proves

`qy_main` is `hmain`: `M₁ = qyM₁ κ` (the kit from `qy_kit_exists`) computes
`fun x => query f g 1^{|x|}` within `qyMainA κ (g n + 1)`:
- `n ≥ 3` (`qy_main_long`): `M₁` hosts the setup (`qy_setup_long`, dispatched at its long exit to
  the locator's anchor), the locator (`qy_loop`, dispatched at its escape: interior and timeout
  to the middle writer, top to the top writer) and the writer, run to its halt
  (`qy_mid_run`/`qy_top_run`, `qy_hosted_halt`). The guards are the phases' segments
  (`qy_mainRed_setup`, `qy_mainRed_loc`). The output is `query_eq`'s word.
- `n ≤ 2` (`qy_main_short`): the setup's short path (`qy_setup_short`, verdict `lt`/`eq`), then
  the halting phase, an emitter of nothing; the query is `[]` (`query_of_not_guard`).
- The initial configuration is the blank seam at the setup's entry (`qy_initCfg`:
  `initCfg_ofWords`, `phaseHostTM_q₀`, the `Cfg.ofWords` equations). The halting run at
  `t ≤ A (g n + 1)` gives `ComputesInTime` at the bound (`computesInTime_iff`,
  `ComputesInTime.mono`).

**`hmain`'s `A`, term by term** (`qyMainA κ = cS + qyLoopA κ + qyWk κ + 8`, each the coefficient
of `g n + 1`, with `n ≤ g n` from `timeConstructible_iff`):
- the setup: `cS = cbA + prA + 2 |bits D₀| + 60` (`qySetB κ n = cS (n + 1)`);
- the locator: `qyLoopA κ = 22 + qyDk κ + 8 · 6⁶ · qyCk κ`, where `22` is the passed rounds'
  rungs (`11 · 2 ℓ_s < 22 n`, `qy_ledger`), `qyDk κ = 134 + 10 · 2^{|bits D₀|} + 2 |bits D₀|` the
  stopping round (the clock's budget `2^m ≤ 2^{|bits D₀|}(2n + 1)`), and `8 · 6⁶ · qyCk κ` the
  arithmetic term (all rounds' polylogarithmic parts, `qyCk κ = 210 + 4 |bits D₀| +
  5 cfA (cfc + 3) + puA + 3 abA`, bounded through `(|bits n| + 1)⁶ ≤ 6⁶ · 4 (n + 1)`);
- the seek, the stage code, the budget field and the writer: `qyWk κ = 4 rC + abA + 2 clA +
  cgA + pbA + 60` (`qy_midB_le`: the seek `rC (n + 4)`, the code's calls `abA (j + 1)`,
  `clA (j + 2)`, `g`'s call `cgA (g n + 1)`, the emissions `6 g n + 4 (j + 1) + 3 (n + 1) + 30`;
  `qy_topB_le`: the square's call `pbA X³` with `X⁴ < 2^{X⁴} = n`);
- `8` for the three dispatch steps and slack.

Here `D₀ = cfA (cfc + 2)`, `m = |bits D₀| + |bits n|`, and the kit's constants are those of its
calls: `cbA` (`bits n`'s input call), `cfA`, `cfc` (`f`'s witness, installed), `puA`, `abA`,
`prA`, `clA`, `pbA` (the install calls of the published rows `polyUnary`, `appendBit`,
`prepend`, `lengthBits`, `polyBits`), `cgA` (`g`'s input call), `rC` (the input seek).

**The target's `C`** as `qy_query_of_main` forms it from `A`: with the guard's decider `D`
(constant `a`, `qy_guard_decider`), the constant machine of `[]` (constant `b`,
`computesFunInTime_const`) and the conditional's constant `c` (`computesFunInTime_cond`),
`C = c · (a + A + b + 1)`.

## `M₁`'s tapes (`QyKit.K`, `QyKit.tp`, the banks)

`K = 16 + cb.k + cf.k + pu.k + 3·ab.k + pr.k + cl.k + pb.k + cg.k`: sixteen named tapes, then one
block per call bank (each call's tape `0` is a named tape, its other tapes its block):
`0` `1^{n+1}` (the input length in unary; the middle's tail); `1` `1^{|bits n|}` (`L + 1` in
unary; `bits n`'s call tape `0`); `2` the rung `1^a`, `a = ℓ + 1`; `3` the next rung; `4`
`1^{X - 1}`; `5` its fourth power `1^{X⁴}` (the `pu` call); `6` the next rung's counter
`0^{X⁴} 1`; `7` `C_f`'s call tape; `8` the clock's counter `1^m`; `9` its saved copy; `10`, `11`
`(j, k) = unpair h` in unary; `12`, `13` the input seek's tapes (`[true]`, blank); `14` `M_g`'s
call tape; `15` a tape that stays blank (the anchor's and the escapes' no-op phases). Layout at
the locator's anchor: `qyLay κ n a j k`.

## Route refinements against the brief (for review)

All within the brief's allowances (private leaves L2, L6; published rows cited instead of new
leaves where a row exists):
- **L2** (`n < f a`): the private leaf `qyCmpTM` compares two tape lengths (lockstep scan, the
  verdict `compare |u| |v|`, a return pass); it is not `Build/Catalog`'s compare row, which
  compares words symbol by symbol, and not `BinaryArith`'s `lt` (value comparison on binary).
  `|bits (f a)| > |bits n|` gives `f a > n`; otherwise `f a < 2 n + 1` and `f a` is expanded to
  unary (`expandTM`, linear) and compared there.
- **L3** (`X > L`, `X⁴` against `L`): no cutoff-product leaf. After the unary test
  `X - 1 < L + 1`, the published install call of `computesFunInTime_polyUnary`
  (`y ↦ 1^{(|y| + 1)⁴}`) on `1^{X - 1}` gives `1^{X⁴}` in `O((L + 1)^5)`, compared with
  `1^{L + 1}` by L2.
- **L4 / the scan folds**: `n ≥ 3` is L2 on `1^{n+1}` and `1^3`; the power-of-two test is not
  needed: when `X⁴ ≤ L` the next rung `2^{X⁴} ≤ n` is built in unary (`appendBit` on `0^{X⁴}`,
  value `2^{X⁴}` by `qy_rung_val`, expanded) and compared with `1^{n+1}`: `lt` next, `eq` top,
  `gt` interior — `qy_decide_spec`'s three cases decided directly.
- **L5** (unpair): `(j, k) = unpair h` is tracked incrementally on tapes `10`, `11` by the
  successor rule of `Nat.unpair`, with `appendBit` install calls and clears; at the escape `j` is
  on tape `10`; the stage code is `bits (j + 1)` by the published `lengthBits` install call on
  `1^{j+1}`, its top bit dropped by the emitter.
- **The counter's tail**: the published prepend install call on `1^{|bits n|}` (instead of
  `writeAdvTM`), saved on tape `9` and copied back each round (`copyMapTM` over a word of the same
  width).
- **The budget field at the top**: the published install call of `computesFunInTime_polyBits`
  (`y ↦ bits ((|y| + 1)²)`) on `1^{X - 1}`, giving `bits (X²) = bits (budget f ℓ)`.

## Every new declaration with its role

211 private declarations (in region (b), after `qy_query_of_main`), listed in `decls.md` by
group with each docstring's first sentence: the probe arithmetic (`QyArith`), the hosted-phase
and row layer (`QyA`), the leaves L2 `qyCmpTM` and L6 `qyEmitTM` with their runs (`QyB`), the
calls, the clock, the expansion and the seek under the host (`QyC`), the call clauses and the kit
`QyKit` (`QyD`), the machine (`QyE`: the tape layout, the phase hosts of the locator, setup, top,
middle and `M₁ = qyM₁ κ`), the setup's run (`QyF`), and the locator's round (`QyG`: the
`bits`-length and `unpair`-successor arithmetic, the clock's bank, the anchor, the escapes, the
scratch, `qy_round_of_seg`, the call; `QyH`: the tests; `QyI`: the cleanup and the pair's update;
`QyJ`: `qy_round`), and the loop (`QyK`: `qy_pow6_le`, the constants `qyCk`, `qyDk`, `qyLoopA`,
the round bounds simplified, `qy_loop`), and the writers' heads (`QyL`: the scratch facts, the
seek `qy_seek_run`, the code's calls `qy_code_calls`, `qy_mid_code`, `qy_top_code`), and the writers (`QyM`: `qy_writer_word`,
`qy_hosted_halt`, `qy_emit_stop`, the bounds `qyMidB`, `qyTopB`, `qy_mid_run`, `qy_top_run`),
and `M₁` (`QyN`: `qy_initCfg`, `qy_mainRed_setup`, `qy_mainRed_loc`, the constants `qyWk`,
`qyMainA`, `qy_midB_le`, `qy_topB_le`, `qy_main_long`, `qy_main_short`, `qy_main`).

**Derived public instance names** (rule 11): `deriving DecidableEq, Fintype` on the seven private
inductives gives 14 public names: `instDecidableEqQyCmp`, `instFintypeQyCmp`,
`instDecidableEqQyEm`, `instFintypeQyEm`, `instDecidableEqQyLK`, `instFintypeQyLK`,
`instDecidableEqQySK`, `instFintypeQySK`, `instDecidableEqQyTK`, `instFintypeQyTK`,
`instDecidableEqQyMK`, `instFintypeQyMK`, `instDecidableEqQyMain`, `instFintypeQyMain`
(`walk.out`, `QYPUBLIC`). `git grep -w` finds none of them anywhere else: not in the tree, not on
`origin/main`, any of the 110 branches or any of the 174 PR heads (Duplication). The ten instances on the phase carriers are named `private instance`s
(`qyLPhFintype`, …). The kit's state instances are `attribute [local instance]`.

## Rule 10 and rule 11

- **Declarations cited outside the file** (elaborated-constant walk, `walk.out`): 166 TCSlib
  constants of other modules reached from the fill's 1,252 constants (types and values): 84
  theorems; 34 definitions (all sealed below); 10 derived instances; 16 projections; 14
  constructors and 8 inductive types. None is private (`_private`: 0). New at checkpoint 3:
  `Turing.Round`, `Turing.round_iff`, `Turing.roundStop`, `Turing.not_mem_roundStop`; at
  checkpoint 4: `Turing.Round.iterate_seq`, `Turing.Round.segment`; at checkpoint 6:
  `Turing.pairEncode` (in the statements) and `Turing.pairEncode_eq`; at checkpoint 7:
  `Turing.initCfg_ofWords`, `Turing.phaseHostTM_q₀`, `Turing.MultiTapeTM.initCfg`,
  `Turing.MultiTapeTM.q₀` (a projection), `Turing.FinTM.computesInTime_iff`.
- **The probe re-run** (`QyImportProbe.lean`, `probe.out`): `EQImportProbe.lean.txt` extended
  by the walk's 75 names not in it: **291 checks of 286 names, 0 errors**.
- **The seal test** (`QySealed.lean`, `sealed.out`): the module with 43 definitions
  `attribute [local irreducible]` from the fill's first private on (the brief's list, the four
  `@[simp]` definitions, and every definition the walk reaches), and `attribute [-simp]` on
  `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`: **0 errors**, the one
  sorry warning only (`exists_diagonalizer`'s), exit 0. The ten instances and the projections are not sealed (instances are
  found by synthesis, projections are reducible structure fields; a seal on four of the instances
  is vacuous: their controls close sealed through structure eta).
- **The controls** (`QySealControls.lean`, `controls.out`): for each of the 43 sealed definitions
  `c`, the goal `c = <its defining value>` closed by `rfl` at default transparency: **43 close
  unsealed, 43 fail sealed** (one `Type mismatch` per control line, lines 95–137).
- **The seal's finding at checkpoint 2, fixed before its zip**: the first seal run rejected four
  hosted-phase lemmas (`qy_hosted`, `qy_hosted'`, `qy_hosted_last`, `qy_hosted_run`) that built or
  projected a `Turing.Segment` by anonymous-constructor notation (unfolding `Segment`); they go
  through `Turing.segment_iff`. The round is built through `Turing.round_iff` and
  `Turing.not_mem_roundStop` for the same reason.
- **The inspection table** (`inspection-table.md`): 498 identifiers passed to
  `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change` in the diff, classified: 95 own file; 45
  other-file theorems; 1 other-file inductive (in a `show`); 100 Core/Mathlib theorems; 5
  constructors and 2 inductives; 2 Core/Mathlib definitions in `show` steps (`Fin.last`,
  `Nat.bits`; allowed; `Nat.pair` is reduced in the `unpair`-successor lemmas' `show` steps, by
  its body); `Function.update` named in `show` goals and inside a `have` nested in a `rw` list
  (reviewed: never a rewrite rule); the simproc `reduceCtorEq`; 244 locals; `Turing.Cfg.ofWords` and
  `Turing.phaseHostTM` named in three `show` goals (`qy_initCfg`, `qy_main_long`,
  `qy_main_short`) that unfold only the file's own `qyM₁` to its `tm` (reviewed: neither is
  unfolded; the sealed copy elaborates with both sealed). **No other-file
  definition is unfolded; no Core or Mathlib definition is passed to `simp`, `rw` or `unfold`.**
  The own leaves `qyCmpTM` and `qyEmitTM` are read through `MultiTapeTM.step_of_some` and the
  `Action.apply_*` field equations (`qy_step`); `step` and `Action.apply` are never unfolded.
- **Rule 11 grep** (`rule11-grep.txt`): the six R3 rows in the diff: 0 hits.

## Checks at the final commit

- **Final sweep** (`checks/final-sweep.log`, the whole order list at `e952bc50`, one module at
  a time, each module's start, end, wall time and maximum RSS): **84 modules OK**,
  01:04:44–01:23:57 UTC (19 m 13 s; summed wall time 1,149 s; maximum RSS 2.94 GB), beside the
  after screen. `NTimeDiagonalizer` (64.4 s, 2.66 GB): zero errors, exactly one sorry warning
  (`exists_diagonalizer` at line 5376), no other warning.
  Every other module: zero errors, and sorry warnings by name exactly the base's (the base's 20
  minus `exists_queryTM`: 19 in 9 modules); their non-sorry warnings are file for file the
  bootstrap's (pre-existing, none in the owned file). The tail check after the last proof edit
  (`checks/tail-check.log`): `NTimeDiagonalizer` 60.4 s, 2.67 GB; `NTimeHierarchy` 15.5 s;
  `Diagonalization` 2.5 s.
- **Lint** (`lint.log`): `style_lint: 0 FAIL, 3 WARN over 5 files` (the base's two, and the owned
  file's size WARN, expected). No line over 100 characters.
- **File size**: 5,402 lines; 22 public and 214 private declarations (211 new) (base: 498; 22 and 3).
- **Owned regions**: the diff adds region (b) (lines 376–5274), rewrites region (d) (the
  Implementation status paragraph, base lines 399–401) and replaces region (c)'s `sorry` (base
  line 410) by `exact qy_main hf hg`; no import added; the three landed privates unchanged.

## Duplication

- **The before screen** (`screens/screen-before.txt`; right after branching, frozen worktree of
  the base, `nice -n 10`): `declarations screened: 1781; copy pairs (target reproduces >= half of source): 2165; reproduced text: 758,766 chars` — equal to the screen base (1,781 declarations, 2,165
  pairs, 758,766 characters).
- **The after screen** (`screens/screen-after.txt`; frozen worktree of `e952bc50`,
  `nice -n 10`, beside the final sweep, 01:04:44–01:40:07 UTC, exit 0): `declarations screened: 1932; copy pairs (target reproduces >= half of source): 2285; reproduced text: 782,065 chars`.
- **New pairs** against the before screen: **120 new, 0 gone**; every new pair has an
  owned-file declaration on one side: 20 cross-file, 100 in-file (the tables below). The first
  after screen, on `323e3588` (kept as `checks/screen-after-323e3588.txt`), found two in-file
  copies, `qy_hosted` against `qy_hosted'` (97–100%) and `qy_embed`, `qy_embed_state` against
  `qy_embed_gen` (91–99%); they were factored (`e952bc50`) and are gone from the final screen.
- **new copies** (pairs at 90% or more): three cross-file — `SeamLayout`'s `sl_unarySplit_copy`
  (100%), `sl_unarySplitTM_run` (99%) and `sl_pairSkip_two_steps` (99%) each reproduce the 85
  characters of `qy_run_one` (`M.runFrom c 1 = M.step c`): the one-step identity, which those
  proofs inline and `CfgRecord` states as its private `recordStep_runFrom_one`; no public lemma
  states it, so this is a re-derivation of another file's private, kept, with a promotion request
  (a public `MultiTapeTM.runFrom_one`); four in-file — `QyKit.bCl`/`QyKit.bAbJ` (95%) and
  `QyKit.bCg`/`QyKit.K` (90%), one-line bank definitions of the same shape by construction;
  `qy_transfer`/`qy_copy` (94%), the readings of two different published rows; and
  `qy_clockHost_finish`/`qy_clock_start` (91%), a shared hypothesis list. No other new pair
  reaches 90%.
**Cross-file pairs (20)**, each with an owned-file declaration on one side:

| target | source | share | disposition |
|---|---|---|---|
| `SeamLayout.lean::sl_unarySplit_copy` | `NTimeDiagonalizer.lean::qy_run_one` | 100% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `SeamLayout.lean::sl_unarySplitTM_run` | `NTimeDiagonalizer.lean::qy_run_one` | 99% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `SeamLayout.lean::sl_pairSkip_two_steps` | `NTimeDiagonalizer.lean::qy_run_one` | 99% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `ExhaustiveReplay.lean::xr_halt_fixed` | `NTimeDiagonalizer.lean::qyC_mapState` | 83% | idiom: the `Cfg.mapState` field equations around `Cfg.ext` (the accepted idiom pairs' pattern; this file's is a third), no lemma re-derived |
| `Encoding.lean::pairDiag_separator` | `NTimeDiagonalizer.lean::qy_run_one` | 75% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `SeamLayout.lean::exists_seamLayoutTM` | `NTimeDiagonalizer.lean::qyC_mapState` | 72% | idiom: the `Cfg.mapState` field equations around `Cfg.ext` (the accepted idiom pairs' pattern; this file's is a third), no lemma re-derived |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_splitEmit_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_scanCopy_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_loopHost_fuel_copy` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean::f2_extract_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `Primitives.lean::splitEmit_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `Primitives.lean::scanCopy_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `Primitives.lean::extract_suffix` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `Primitives.lean::emitterToken_separator` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `Loop.lean::loopHost_fuel_copy` | `NTimeDiagonalizer.lean::qy_run_one` | 71% | idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic` |
| `SeamLayout.lean::sl_rewrap` | `NTimeDiagonalizer.lean::qyC_mapState` | 70% | idiom: the `Cfg.mapState` field equations around `Cfg.ext` (the accepted idiom pairs' pattern; this file's is a third), no lemma re-derived |
| `ExhaustiveReplay.lean::xr_phase_step` | `NTimeDiagonalizer.lean::qyC_mapState` | 69% | idiom: the `Cfg.mapState` field equations around `Cfg.ext` (the accepted idiom pairs' pattern; this file's is a third), no lemma re-derived |
| `NTimeDiagonalizer.lean::qyEmitTM` | `Simulation.lean::emitAction` | 66% | idiom: the model's one-symbol emission action; `FinTM.emitAction` halts at its chain's end, which the emitter's prefix cannot (it continues to its scan), so it is not reusable here |
| `NTimeDiagonalizer.lean::qy_call` | `SeamLayout.lean::sl_rewrap` | 52% | idiom: `seamReleaseTM_runFrom_pos` and the `Cfg.mapState` field equations around a seam (`SeamLayout` is a model to read; no lemma re-derived) |
| `NTimeDiagonalizer.lean::qy_cmp_run` | `Nondeterminism.lean::b2_unary_run` | 50% | idiom: a run lemma's statement shape over a unary tape; a different machine (L2's comparator against `Nondeterminism`'s unary decider) |

**In-file pairs (100)**, each with its justification:

| target | source | share | justification |
|---|---|---|---|
| `QyKit.bCl` | `QyKit.bAbJ` | 95% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_transfer` | `qy_copy` | 94% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_clockHost_finish` | `qy_clock_start` | 91% | the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions |
| `QyKit.bCg` | `QyKit.K` | 90% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qyTestS` | `qyTestP` | 89% | two explicit time bounds of the same shape, for different runs |
| `qyRndS` | `qyTestP` | 89% | two explicit time bounds of the same shape, for different runs |
| `QyKit.bCg` | `QyKit.bPb` | 88% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_call` | `qyC_mapState` | 86% | the `Cfg.mapState` field-equation idiom around a seam (`qy_call`'s conversions) |
| `QySpec` | `QyInSpec` | 85% | the call clauses: an install call (an argument), an input call (the blank seam), the clocked call (its two exits); one statement each |
| `QyKit.bPb` | `QyKit.bCl` | 85% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCg` | `QyKit.bCl` | 85% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPb` | `QyKit.bPr` | 85% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCl` | `QyKit.bPr` | 85% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCg` | `QyKit.bPr` | 85% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qyRndS` | `qyTestS` | 85% | two explicit time bounds of the same shape, for different runs |
| `QyInSpec` | `QySpec` | 85% | the call clauses: an install call (an argument), an input call (the blank seam), the clocked call (its two exits); one statement each |
| `QyKit.bPb` | `QyKit.bAbK` | 84% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyClockSpec` | `QySpec` | 84% | the call clauses: an install call (an argument), an input call (the blank seam), the clocked call (its two exits); one statement each |
| `QyKit.bPr` | `QyKit.bAbK` | 83% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCl` | `QyKit.bAbK` | 83% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCg` | `QyKit.bAbK` | 83% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPb` | `QyKit.bAbJ` | 83% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPb` | `QyKit.bAb0` | 83% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPb` | `QyKit.bCg` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPr` | `QyKit.bAbJ` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCg` | `QyKit.bAbJ` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPr` | `QyKit.bAb0` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCl` | `QyKit.bAb0` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bCg` | `QyKit.bAb0` | 82% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qyTestP` | `qyTestS` | 82% | two explicit time bounds of the same shape, for different runs |
| `QyKit.bCl` | `QyKit.bPb` | 81% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_two_pow_bits_le` | `qy_log_bits` | 81% | `Nat.bits` length facts, each through `qy_log_bits`'s `Nat.log` reading |
| `QyKit.bPr` | `QyKit.bCl` | 80% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bAbK` | `QyKit.bPr` | 79% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_unpair_succ_gt` | `qy_unpair_succ_last` | 79% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `QyKit.bAbJ` | `QyKit.bCl` | 79% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_copy_over` | `qy_copy` | 77% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `QyKit.bCl` | `QyKit.bCg` | 77% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bPr` | `QyKit.bPb` | 76% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_transfer` | `qy_clear` | 75% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_not_scratch_ge` | `qy_not_scratch_tp` | 75% | the two off-scratch facts (bank blocks, named tapes): the same case split on the clock's bank |
| `qy_unpair_succ_last` | `qy_unpair_succ_gt` | 75% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `qy_ones_val` | `qy_rung_val` | 74% | the counter values of `1^m` and `0^m 1`, each by induction on `m` |
| `qy_copy_over` | `qy_clear` | 74% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `QyKit.bAbK` | `QyKit.bCl` | 74% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_rndS_le` | `qy_rndP_le` | 73% | the stopping and the passed round's bound simplifications: same expansion pattern, different bounds |
| `QyKit.bAbJ` | `QyKit.bPr` | 73% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qyTestS` | `qyRndS` | 72% | two explicit time bounds of the same shape, for different runs |
| `qy_mid_run` | `qy_top_run` | 72% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `QyClockSpec` | `QyInSpec` | 72% | the call clauses: an install call (an argument), an input call (the blank seam), the clocked call (its two exits); one statement each |
| `QyKit.bPr` | `QyKit.bCg` | 72% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_transfer` | `qy_copy_over` | 71% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `QyKit.bAbK` | `QyKit.bPb` | 71% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_copy` | `qy_copy_over` | 71% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_top_run` | `qy_mid_run` | 71% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qy_mid_code` | `qy_top_code` | 70% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qyTestP` | `qyRndS` | 70% | two explicit time bounds of the same shape, for different runs |
| `qy_copy` | `qy_writeConst` | 69% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_setup_long` | `qy_setup_short` | 69% | the long and short paths through the same host: the short one is a prefix of the long one's phases |
| `qy_main_long` | `qy_main_short` | 69% | the long and short paths through the same host: the short one is a prefix of the long one's phases |
| `qy_expandHost` | `qy_expand_start` | 69% | the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions |
| `qy_midB_le` | `qy_topB_le` | 69% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qy_rung_val` | `qy_ones_val` | 68% | the counter values of `1^m` and `0^m 1`, each by induction on `m` |
| `qy_hosted_last` | `qy_hosted'` | 68% | the phase host's segment with and without a final dispatch (`phaseHostTM_run` against `phaseHostTM_run_le`) |
| `qy_transfer` | `qy_writeConst` | 68% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_ledger` | `qy_sum_affine` | 67% | two sums over `Finset.range`, each by `Finset.sum_range_succ` induction |
| `QyKit.bAb0` | `QyKit.bPr` | 67% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bAbK` | `QyKit.bCg` | 66% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bAbJ` | `QyKit.bPb` | 66% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_copy` | `qy_clear` | 65% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `QyKit.bAbK` | `QyKit.bAbJ` | 65% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_hosted'` | `qy_hosted_last` | 64% | the phase host's segment with and without a final dispatch (`phaseHostTM_run` against `phaseHostTM_run_le`) |
| `qy_unpair_succ_lt` | `qy_unpair_succ_last` | 64% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `QyMPh` | `QyTPh` | 64% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qyAt2_move` | `qy_moveOne` | 63% | head-move equations for the comparator and for one tape |
| `qy_sum_affine` | `qy_ledger` | 63% | two sums over `Finset.range`, each by `Finset.sum_range_succ` induction |
| `qy_rndP_le` | `qy_rndS_le` | 63% | the stopping and the passed round's bound simplifications: same expansion pattern, different bounds |
| `QyKit.bAb0` | `QyKit.bCl` | 63% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_unpair_succ_gt` | `qy_unpair_succ_lt` | 62% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `QyKit.bAbJ` | `QyKit.bCg` | 61% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_unpair_succ_lt` | `qy_unpair_succ_gt` | 61% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `qy_unpair_succ_last` | `qy_unpair_succ_lt` | 61% | the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case |
| `QyTPh` | `QyMPh` | 61% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qyMidM` | `qyTopM` | 61% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `QyKit.bAbJ` | `QyKit.bAbK` | 61% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `QyKit.bAb0` | `QyKit.bPb` | 60% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_clear` | `qy_copy_over` | 60% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_not_scratch_tp` | `qy_not_scratch_ge` | 58% | the two off-scratch facts (bank blocks, named tapes): the same case split on the clock's bank |
| `qy_clear` | `qy_copy` | 58% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_copy_over` | `qy_writeConst` | 56% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `QyKit.bAb0` | `QyKit.bCg` | 56% | two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets |
| `qy_clear` | `qy_writeConst` | 56% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_clock_start` | `qy_expand_start` | 54% | the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions |
| `qy_loop` | `qy_notStop` | 53% | the escape set's membership test (`qyLocE`) read in both |
| `qy_copy` | `qy_transfer` | 53% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_writeConst` | `qy_copy` | 53% | two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints |
| `qy_topB_le` | `qy_midB_le` | 52% | the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts |
| `qy_expandHost` | `qy_wordPatch_ones` | 52% | the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions |
| `qy_two_pow_bits_le` | `qy_lt_two_pow_bits` | 51% | `Nat.bits` length facts, each through `qy_log_bits`'s `Nat.log` reading |
| `qy_clockHost_finish` | `qy_expand_start` | 50% | the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions |

- **The semantic search** (the appendix table, one row per new private): by name, `git grep -w`
  of all 211 new names and the 14 derived instance names over the tree, `origin/main`, all 110
  branches and all 174 PR heads (open and closed): **0 hits** outside the owned file. By
  statement, `git grep` of distinctive fragments of the statements that do not mention the
  file's own definitions (`dup/stmt-patterns.tsv`, hits in `dup/stmt-hits.txt`). By `exact?`, on
  each of the 129 new private theorems' statements in a scratch copy of the module
  (`dup/QyExactProbe.lean`, `dup/exactq.out`, run on checkpoint 7's tree; the statements are
  unchanged since, and the four removed privates among them): 118 not closed, one timed out
  (`qy_rndP_le`), 10 closed — 7 by `rfl` (definitional, no declaration; two of them the removed
  `qyEmb2_zero`, `qyEmb2_one`), `qy_installSpec` by `FinTM.exists_installCallTM` (its own
  proof: the published contract read through the clause `QySpec`), `QyKit.tp_inj` by a generic
  order lemma through the own `QyKit.tp`, and **`QyKit.tape_cases` by
  `Classical.exists_or_forall_not`: a re-derivation of a published lemma, fixed** (its proof now
  cites it).
- **Statements published outside the base or the import closure** (not citable; kept, listed as
  dedup candidates): `qy_bits_len_mono` (`Complexity.LogProg.length_bits_mono`,
  `SpaceComplexity/Machines/Bin.lean`, at the base, outside the closure); `qy_lt_two_pow_bits`,
  `qy_two_pow_bits_le` (`lt_two_pow_bits`, `two_pow_bits_le`, `Randomized/SpaceAmplifyPoly.lean`,
  on `origin/main`, `complexity/arora-barak-ch7` and PR 135 only).
- **The BinaryArith ledger** (`origin/main`, #135; not in the tree): its `lt`, `le`
  (`AddSub.lean`: `decide (bitsVal a < bitsVal b)` on `pairEncode a b`, `PolyTimeComputable`)
  are function-level value comparisons in polynomial time; L2 is a tape-level row comparing two
  tapes' lengths in place in linear time, with a verdict state for the phase host. Its unary
  `mulU` (`Loops.lean`, `|a| · |b|`) is the nearest to L3's cutoff product, which this fill does
  not write: the fourth power is the published `polyUnary` install call. Neither is cited
  (not at the base).
- **Known hazards checked**: the clock's two exits are read through the kit's `QyClockSpec`, built
  once from `exists_stepClockTMVia`'s clauses (no `xr_` prelude); the calls through their
  contracts (no `emCall_*`); the `Cfg.mapState` field-equation idiom appears in `qyC_mapState`
  and the call's seam conversions (`qy_call`) only.

## The leaves and the scan folds

- **L1** (the guard's decider): landed at the base (`qy_guard_decider`), unchanged.
- **L2, the length comparator** (`qyCmpTM K a b`, `QyCmp`): a lockstep scan of tapes `a` and
  `b`, the verdict `compare |u| |v|`, a return pass; run `qy_cmp_run` (time
  `2 min(|u|, |v|) + 2`, heads back at `0`, tapes unchanged, first reaching `done` at the end).
  Its docstring says which rows it is not: the catalog's compare row compares words symbol by
  symbol, and the walk rows move heads without a verdict. Uses: `n ≥ 3` (`1^{n+1}` against
  `1^3`), `|bits (f a)|` against `|bits n|`, `X − 1` and `X⁴` against `|bits n|`, `ℓ' + 1`
  against `n + 1`, and `j` against `k` for the pair's update.
- **L3** (`X > L`, the cutoff product): not written as a leaf; the published install call of
  `FinTM.computesFunInTime_polyUnary` (`y ↦ 1^{(|y|+1)⁴}`) on `1^{X − 1}`, after L2 has checked
  `X − 1 < |bits n|`, gives `1^{X⁴}` in `O((L + 1)⁵)`.
- **L4 / the scan folds**: `n ≥ 3` is L2 (above); the power-of-two test is not needed, since the
  next rung `2^{X⁴}` is built in unary only when `X⁴ < |bits n|` (so `2^{X⁴} ≤ n`) and compared
  with `1^{n+1}` by L2.
- **L5** (`Nat.unpair`): not written as a leaf; the pair `(j, k) = unpair h` is kept in unary on
  tapes `10`, `11` and advanced each passed round by the successor rule (`qy_rnd_pair`, the four
  `qy_unpair_succ_*` lemmas), with the published `appendBit` install call and `clearTM`.
- **L6, the emitter** (`qyEmitTM K i pre suf rr dl`, `QyEm`): a prefix, tape `i`'s word
  (without its last bit when `dl`) with every bit written `rr + 1` times, a suffix; the `done`
  state's action halts. Runs `qy_emit_run` (to `done`, `≤ |pre| + |suf| + 3 + |w| (rr + 3)`
  steps) and `qy_emit_stop` (one more step, halted). Its docstring says why no public row
  serves: it is `FinTM.emitAction`'s fixed-word emission chain around a one-tape scan, and no
  public row emits a tape word with repetition.

## The calls

- **Every call is released** at its entry by `seamReleaseTM` and read through
  `seamReleaseTM_runFrom_pos` (`qy_call`, then `qy_callHost` under R1's `embedEmitTM`): the
  released machine starts at the fresh state `Sum.inl ()` and runs the call at every positive
  time, so `entry = exit` needs no split (the first stop is `Sum.inr exit`, off the fresh state).
  The install calls (`exists_installCallTM`: `f`'s witness, `polyUnary`, `appendBit`, the
  counter's `prepend`, `lengthBits`, `polyBits`) start from `Cfg.ofWords entry (stateWord k arg)`
  on a bank whose tape `0` holds the argument and whose other tapes are blank
  (`qy_arg_bank`); the input calls (`exists_inputCallTM`: `bits n` and `g`'s witness) from the
  blank seam (`qy_blank_bank`).
- **The clocked call** (`qy_clockHost_finish`, `qy_clockHost_timeout`, over the kit's
  `QyClockSpec` from `exists_stepClockTMVia`): `f`'s witness, released, on the bank of tape `7`,
  the counter `1^m` on tape `8`. Finish: `bits (f a)` on tape `7`, a word of width `m` on tape
  `8`, the input head at `1`. Timeout: the timeout family `tmo r` dispatches to the timeout
  escape, **the timed-out call is silent** (the clock's timeout clause: output `[]`, so the
  configuration's output is unchanged) and every tape off the clock's bank is untouched; the
  input head is unknown.
- **The input seek after the loop** (`qy_seek_run`): the middle writer's first phase returns the
  input head to `1` from any position (the kit's seek clause on tapes `12`, `13`); the top
  escape already has it at `1`.

## Edge cases

| case | covered by |
|---|---|
| `n ≤ 2` (the setup's short-circuit) | `qy_setup_short` (verdict `lt`/`eq`), `qy_main_short` (output `[]`, `query_of_not_guard`) |
| `n = 3` | `stage f 3 = 0`: no passed round; `qy_loop` with `s = 0` (`Round.iterate_seq` over the empty range), the stopping round from `qyAt κ x 0` |
| a top `n = ladder f (i + 1)` | `qy_rnd_tests`'s `eq` verdict at `r16`, `qy_loop`'s top case, `qy_top_run`, `qy_main_long` (`query_eq`'s top branch, `budget_eq`) |
| the first stage `i = 0` | `qyAt κ x 0` is the setup's long exit layout (`ladder_zero`, `Nat.unpair_zero`) |
| `f a > n` by a timeout | `qy_rnd_call`'s timeout (`qy_timeout_cert`), the dirty bank off `QyEscT`'s tapes, `qy_seek_run` |
| `f a > n` by a fast witness with a large output | `r3`: `|bits (f a)| > |bits n|` gives `f a > n` (`qy_bits_len_mono`), the interior escape |
| `X > L` | `r7`: `X − 1 ≥ |bits n|` gives `2^{X⁴} ≥ 2^{|bits n|} > n`, the interior escape |
| `X⁴ = L` with `n` not a power of two | `X⁴ < |bits n|`, so the next rung `2^{X⁴} < n` is built and `r16`'s `lt` passes the round |
| `g n = n` | only `n ≤ g n` is used (`qy_midB_le`, `qy_main_long`, `qy_main_short`) |

## Promotion candidates and escalations

**Escalations: none.** **Promotion candidates** (each a private leaf or lemma with no published
counterpart in the import closure):
- L2 `qyCmpTM` with `qy_cmp_run` (a framed length comparison with verdict) and L6 `qyEmitTM`
  with `qy_emit_run`/`qy_emit_stop` (a repeating emitter) — row candidates for `Build/Catalog`;
- the phase-host segment forms `qy_hosted`, `qy_hosted'`, `qy_hosted_last`, `qy_hosted_halt`
  and `qy_round_of_seg` — candidates for `Build/Seam` and `Build/Contract/Basic`;
- the `Nat.unpair` successor rule (`qy_unpair_succ_lt`, `_last`, `_diag`, `_gt`) — no Mathlib
  counterpart;
- `qy_run_one` (`M.runFrom c 1 = M.step c`) — inlined across the catalog, private in `CfgRecord`
  (`recordStep_runFrom_one`): a public `MultiTapeTM.runFrom_one` would serve all;
- `qy_bits_len_mono`, `qy_lt_two_pow_bits`, `qy_two_pow_bits_le`, `qy_log_bits`: identical or
  near statements exist outside the closure (`Complexity.LogProg.length_bits_mono`,
  `length_bits_le_log` in `SpaceComplexity/Machines/Bin.lean`; `lt_two_pow_bits`,
  `two_pow_bits_le` in `Randomized/SpaceAmplifyPoly.lean` on `origin/main`): a shared
  `Nat.bits` arithmetic file would remove the copies.

## Proposed `**Implementation.**` paragraph (for the maintainer)

**Implementation.** The guard (`qy_guard`, `qy_guard_decider`, `qy_query_of_main`) reduces the
query to a machine computing it on the unary word of every input's length within
`A · (g n + 1)`; that machine (`qyM₁ κ`, over the kit `QyKit` of calls) is the phase host of a
setup, a locator and two writers (`qy_main`). The setup computes `bits n` by the input call,
`1^{n+1}` by `expandTM`, the first rung, the test `n ≥ 3` (the private comparator L2), the input
seek's tape and an all-ones clock counter of width `|bits n| + |bits D₀|` (`qy_setup_long`,
`qy_setup_short`). Each locator round (`qy_round`, a `Turing.Round` at its anchor with interior,
top and timeout escapes) runs `f`'s witness under the step clock on `1^a`, tests
`|bits (f a)|`, `X − 1` and `X⁴` against `|bits n|` (`X = f a + a + 1`; the fourth power by the
`polyUnary` install call), builds the next rung `2^{X⁴} ≤ n` in unary and compares it with
`1^{n+1}`; a passed round cleans up and advances `unpair h` by its successor rule. The loop
(`qy_loop`, `Turing.Round.iterate_seq`) stops at the stage `stage f n` within a linear bound, the
passed rungs summing to `2 ℓ_s` (`qy_ledger`) and the polylogarithmic terms linear by
`x⁶ ≤ 6⁶ · 2^x`. The writers (`qy_mid_run`, `qy_top_run`) seek the input head home, compute
`bits (j + 1)` for the stage code, run `g`'s witness or the budget's square, and emit
`b :: ⟨⟨B, α⟩, t⟩` with the private emitter L6 (`qy_writer_word`).

## Process notes and deviations

- **One Lean process at a time** throughout (every check, probe, seal, control, axiom print and
  sweep sequential); the screens (Python) ran beside the bootstrap and the final sweep, as
  allowed.
- **The worker process was restarted twice** after checkpoint 7's delivery: once during the
  semantic duplication probe's run (the interrupted probe was re-run from the start), and once
  after the final sweep and the after screen had both finished (their outputs were complete).
  The clone, the branch and all evidence survived both.
- **The semantic probe's mechanics**: the CLI prints `exact?`'s successes without a position, and
  the in-file `maxErrors` option does not lift the CLI's cap of 100 errors, so the final probe
  wraps each `exact?` as `first | exact? | sorry` (a failure leaves a positioned sorry warning)
  and attributes the successes in source order (`parse_exactq.py`). `qy_rndP_le`'s `exact?` ran
  out of heartbeats (an uncaught timeout, recorded as not closed).
- **Open-PR scope**: the GitHub API is not available for this repository in this session (read
  access is the anonymous git lane), so open PRs could not be told from closed ones; the by-name
  and by-statement searches therefore ran over **all 174 PR heads** (a superset), all 110
  branches and `origin/main`.

## Appendix: the semantic search, per new private

By name: `git grep -w` of all 211 new names and the 14 derived instance names over the tree, `origin/main`, all 110 branches and all 174 PR heads (open and closed): 0 hits outside the owned file.

| new private | kind | by name | by statement | `exact?` |
|---|---|---|---|---|
| `qy_ladder_succ_eq` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_ledger` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_ones_val` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_rung_val` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_ones_ge` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_two_pow_bits_le` | theorem | 0 hits | `two_pow_bits_le` (`Randomized/SpaceAmplifyPoly.lean`) states it on `origin/main`, `complexity/arora-barak-ch7` and PR 135 only, not at the base: not citable; kept | could not close the goal |
| `qy_log_bits` | theorem | 0 hits | `length_bits_le_log` (`Bin.lean`) states the `≤` half only, outside the import closure | could not close the goal |
| `qy_call_bound` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_two_pow_le_ladder` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_stage_lt_log` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_timeout_cert` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qyC` | def | 0 hits | — | — (a definition) |
| `qyC_mapState` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | closed by `exact rfl` (definitional); the file's proof reads `Cfg.mapState` through its field equations (the seal) |
| `qy_hosted` | theorem | 0 hits | the phase host's segment form: `phaseHostTM_run` (cited) states the run, no segment form | could not close the goal |
| `qy_hosted'` | theorem | 0 hits | as `qy_hosted` | could not close the goal |
| `qy_hosted_last` | theorem | 0 hits | as `qy_hosted` (`phaseHostTM_run_le`, cited) | could not close the goal |
| `qy_hosted_run` | theorem | 0 hits | as `qy_hosted` | could not close the goal |
| `qy_patch_end` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_bufferTape_map` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_guard_of_cut` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_copy` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_copy_over` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_transfer` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_clear` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_writeConst` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_rewind` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_embed` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_embed_state` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_call` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_callHost` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_step` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyCmp` | inductive | 0 hits | — | — (a definition) |
| `qyCmpTM` | def | 0 hits | — | — (a definition) |
| `qyAt2` | def | 0 hits | — | — (a definition) |
| `qyAt2_move` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_cmp_run` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyEm` | inductive | 0 hits | — | — (a definition) |
| `qyEmitTM` | def | 0 hits | — | — (a definition) |
| `qyBody` | def | 0 hits | — | — (a definition) |
| `qy_noMove` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_moveOne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_run_one` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | closed by `exact rfl` (definitional; no declaration) |
| `qy_run_two` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | closed by `exact rfl` (definitional; no declaration) |
| `qy_emit_run` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_release_first_stop` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_call_output_nil` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_clocked_call` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_wordPatch_ones` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_embed_gen` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyClockSpec` | def | 0 hits | — | — (a definition) |
| `qy_clock_start` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_clockHost_finish` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_clockHost_timeout` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_expand_start` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_expandHost` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_seekHost` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_emit_halt` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QySpec` | def | 0 hits | — | — (a definition) |
| `QyInSpec` | def | 0 hits | — | — (a definition) |
| `QySpec.mono` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_installSpec` | theorem | 0 hits | is `FinTM.exists_installCallTM` read through the own clause `QySpec`; its proof cites it | closed by `FinTM.exists_installCallTM` (its own proof) |
| `qy_inputSpec` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit` | structure | 0 hits | — | — (a definition) |
| `qy_pow_mono` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_kit_exists` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.K` | def | 0 hits | — | — (a definition) |
| `QyKit.le_K` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.tp` | def | 0 hits | — | — (a definition) |
| `QyKit.tp_inj` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | closed by a generic order lemma up to unfolding the own `QyKit.tp`; no statement about it is published |
| `qyBank` | def | 0 hits | — | — (a definition) |
| `qyBank_zero` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | closed by `exact rfl` (the own definition) |
| `qyBank_val` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qyEmb2` | def | 0 hits | — | — (a definition) |
| `QyKit.tp_val` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | closed by `exact rfl` (the own definition) |
| `QyKit.bCb` | def | 0 hits | — | — (a definition) |
| `QyKit.bCf` | def | 0 hits | — | — (a definition) |
| `QyKit.bPu` | def | 0 hits | — | — (a definition) |
| `QyKit.bAb0` | def | 0 hits | — | — (a definition) |
| `QyKit.bAbJ` | def | 0 hits | — | — (a definition) |
| `QyKit.bAbK` | def | 0 hits | — | — (a definition) |
| `QyKit.bPr` | def | 0 hits | — | — (a definition) |
| `QyKit.bCl` | def | 0 hits | — | — (a definition) |
| `QyKit.bPb` | def | 0 hits | — | — (a definition) |
| `QyKit.bCg` | def | 0 hits | — | — (a definition) |
| `QyKit.bClk` | def | 0 hits | — | — (a definition) |
| `QyKit.tp_ne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyLK` | inductive | 0 hits | — | — (a definition) |
| `QyLPh` | abbrev | 0 hits | — | — (a definition) |
| `qyLPhFintype` | instance | 0 hits | — | — (a definition) |
| `qyLPhDecEq` | instance | 0 hits | — | — (a definition) |
| `qyLocM` | def | 0 hits | — | — (a definition) |
| `qyLocRed` | def | 0 hits | — | — (a definition) |
| `qyLoc` | def | 0 hits | — | — (a definition) |
| `QySK` | inductive | 0 hits | — | — (a definition) |
| `QySPh` | abbrev | 0 hits | — | — (a definition) |
| `qySPhFintype` | instance | 0 hits | — | — (a definition) |
| `qySPhDecEq` | instance | 0 hits | — | — (a definition) |
| `qySetM` | def | 0 hits | — | — (a definition) |
| `qySetRed` | def | 0 hits | — | — (a definition) |
| `qySet` | def | 0 hits | — | — (a definition) |
| `QyTK` | inductive | 0 hits | — | — (a definition) |
| `QyTPh` | abbrev | 0 hits | — | — (a definition) |
| `qyTPhFintype` | instance | 0 hits | — | — (a definition) |
| `qyTPhDecEq` | instance | 0 hits | — | — (a definition) |
| `qyTopM` | def | 0 hits | — | — (a definition) |
| `qyTopRed` | def | 0 hits | — | — (a definition) |
| `qyTop` | def | 0 hits | — | — (a definition) |
| `QyMK` | inductive | 0 hits | — | — (a definition) |
| `QyMPh` | abbrev | 0 hits | — | — (a definition) |
| `qyMPhFintype` | instance | 0 hits | — | — (a definition) |
| `qyMPhDecEq` | instance | 0 hits | — | — (a definition) |
| `qyMidM` | def | 0 hits | — | — (a definition) |
| `qyMidRed` | def | 0 hits | — | — (a definition) |
| `qyMid` | def | 0 hits | — | — (a definition) |
| `QyMain` | inductive | 0 hits | — | — (a definition) |
| `QyMainPh` | abbrev | 0 hits | — | — (a definition) |
| `qyMainPhFintype` | instance | 0 hits | — | — (a definition) |
| `qyMainPhDecEq` | instance | 0 hits | — | — (a definition) |
| `qyMainM` | def | 0 hits | — | — (a definition) |
| `qyMainRed` | def | 0 hits | — | — (a definition) |
| `qyM₁` | def | 0 hits | — | — (a definition) |
| `QyKit.m` | def | 0 hits | — | — (a definition) |
| `qyLay` | def | 0 hits | — | — (a definition) |
| `QyKit.tape_cases` | theorem | 0 hits | proof cites `Classical.exists_or_forall_not` (the probe's finding, fixed) | closed by `Classical.exists_or_forall_not`: now cited |
| `qyBank_ne_tp` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qySetF` | def | 0 hits | — | — (a definition) |
| `qySetB` | def | 0 hits | — | — (a definition) |
| `qy_bits_val` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_blank_bank` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_arg_bank` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.bPr_ne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qySetT5` | def | 0 hits | — | — (a definition) |
| `qy_setup_head` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_setup_long` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_setup_short` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_bits_len_mono` | theorem | 0 hits | `Complexity.LogProg.length_bits_mono` (`SpaceComplexity/Machines/Bin.lean`, at the base) states it, outside the frozen import closure: not citable; kept (relocation candidate) | could not close the goal |
| `qy_lt_two_pow_bits` | theorem | 0 hits | `lt_two_pow_bits` (`Randomized/SpaceAmplifyPoly.lean`) states it on `origin/main`, `complexity/arora-barak-ch7` and PR 135 only, not at the base: not citable; kept | could not close the goal |
| `qy_unpair_succ_lt` | theorem | 0 hits | no `Nat.unpair` successor lemma in Mathlib or the tree | could not close the goal |
| `qy_unpair_succ_last` | theorem | 0 hits | as `qy_unpair_succ_lt` | could not close the goal |
| `qy_unpair_succ_diag` | theorem | 0 hits | as `qy_unpair_succ_lt` | could not close the goal |
| `qy_unpair_succ_gt` | theorem | 0 hits | as `qy_unpair_succ_lt` | could not close the goal |
| `QyKit.bClk_castSucc` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.bClk_last` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.bCf_ne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.bPu_ne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.bAb0_ne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.bAbJ_ne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.bAbK_ne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qyLayT` | def | 0 hits | — | — (a definition) |
| `qyAnc` | def | 0 hits | — | — (a definition) |
| `QyLK.isEsc` | def | 0 hits | — | — (a definition) |
| `qyLocE` | def | 0 hits | — | — (a definition) |
| `qy_notStop` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_esc_mem` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qyScratch` | def | 0 hits | — | — (a definition) |
| `QyEscT` | def | 0 hits | — | — (a definition) |
| `qy_tp7_mem` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_tp8_mem` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_not_scratch` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_round_of_seg` | theorem | 0 hits | `Turing.Round.of_cut` (a cut predicate, one escape) is the nearest; no first-step + segment form | could not close the goal |
| `qy_rnd_call` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qyTA` | def | 0 hits | — | — (a definition) |
| `qyTB` | def | 0 hits | — | — (a definition) |
| `qyTestS` | def | 0 hits | — | — (a definition) |
| `qyTestP` | def | 0 hits | — | — (a definition) |
| `qy_rnd_tests` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_rnd_clean` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_layT_pair` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_rnd_pair` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qyRndP` | def | 0 hits | — | — (a definition) |
| `qyRndS` | def | 0 hits | — | — (a definition) |
| `qy_round` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_pow6_le` | theorem | 0 hits | nearest `succ_pow_le_two_pow_mul` (`Randomized/ZPPHostsClasses.lean`, `origin/main`): a different bound | could not close the goal |
| `qy_sum_affine` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qyCk` | def | 0 hits | — | — (a definition) |
| `qyDk` | def | 0 hits | — | — (a definition) |
| `qyLoopA` | def | 0 hits | — | — (a definition) |
| `qy_rndP_le` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | `exact?` ran out of heartbeats (400000): not closed |
| `qy_rndS_le` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qyAt` | def | 0 hits | — | — (a definition) |
| `qy_loop` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_not_scratch_ge` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_not_scratch_tp` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_bank_not_scratch` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyEscT.tp` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyEscT.bank` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.bCl_ne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_code_calls` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_seek_run` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_mid_code` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_top_code` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_flatMap_dbl_dbl` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_writer_word` | theorem | 0 hits | `pairEncode_pairEncode_length`/`_drop` (`Build/InputDevice.lean`): length and drop facts, not the expansion; `pairEncode_eq` is cited | could not close the goal |
| `qy_hosted_halt` | theorem | 0 hits | `phaseHostTM_run_le` (cited) has no halting form | could not close the goal |
| `qy_emit_stop` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.bCg_ne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `QyKit.bPb_ne` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qyMidB` | def | 0 hits | — | — (a definition) |
| `qyTopB` | def | 0 hits | — | — (a definition) |
| `qy_mid_run` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_top_run` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_initCfg` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_mainRed_setup` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_mainRed_loc` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qyWk` | def | 0 hits | — | — (a definition) |
| `qyMainA` | def | 0 hits | — | — (a definition) |
| `qy_midB_le` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_topB_le` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_main_long` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_main_short` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
| `qy_main` | theorem | 0 hits | no other file states it (statement over the file's own definitions, or no fragment hit) | could not close the goal |
