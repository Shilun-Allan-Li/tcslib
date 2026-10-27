<!-- DRAFT (maintainer, 2026-10-27), from the issued `eq-fill-query.md` and the review of megafill
D's partial (`campaign/fills/eq/reviews/fill-cp1/REVIEW.md`, "The continuation"). **The user's
rulings (2026-10-27):** E-SERIAL is not a deviation (addendum v2.6 adopted); E-DUP by an API PR
first (PR #171, `Build/WordTests`, every copy re-pointed); checkpoint 1 lands with E1–E5, its guard
citing #171's rows; **cont1 goes to Claude, as a standalone fill** (not a megafill item). To fill at
issue, from the pre-ship at the issue commit on the landed tree (after #171 and the landing): every
⟨…⟩ (the issue commit @ANCESTOR@; the two PRs and their merges; the blob; the line numbers; the
order list, roots and base sorry set; the probes' counts; the screen base; the lint base). Then a
review sub-agent, then issue. Remove this comment at issue. -->

# Ch3–4 fill campaign — E-Q cont1, the stage query's main machine (`Turing.NTimeDiag.exists_queryTM`, `Diagonalization/NTimeDiagonalizer.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement**: the C1-E statement gate (gate 39, round 2,
    `campaign/gates/39-ntime-diag-statements/`; its note 8 is `exists_queryTM`), unchanged by
    gate 45;
  - **the chapter predicates' readings (A1, PR #164)**: `Complexity.timeConstructible_iff`
    (`ClassP/TimeConstructible`), the only route by which a proof may unpack
    `Complexity.TimeConstructible`;
  - **the sequence form of round iteration (PR #167)**: `Turing.Round.iterate_seq`
    (`Build/Contract/Basic`), rounds given as a sequence of configurations with per-round times,
    their segment over the summed time;
  - the step clock `Turing.exists_stepClockTMVia` (`Build/StepClock`), the install and input calls
    `Turing.FinTM.exists_installCallTM` (`Build/Loop`) and `Turing.FinTM.exists_inputCallTM`
    (`Build/InputCall`), the function-level conditional `Turing.FinTM.computesFunInTime_cond`
    (`Build/Wrappers`), and the catalog's framed rows;
  - **checkpoint 1, landed** (PR #173, gate 83; megafill D's partial): your file's imports (the
    eight of the first round and `Build/WordTests`), `qy_guard`, `qy_guard_decider` (the guard's
    decider, L1) and `qy_query_of_main`, which reduces the target to the main machine's contract
    `hmain` (below);
  - **the linear word tests** (PR #171, `Build/WordTests`):
    `Turing.FinTM.computesFunInTime_decideEq` (equality with a fixed word, as `[decide (x = w)]`)
    and `Turing.FinTM.computesFunInTime_allTrue`; the guard cites both. Use them wherever a leaf
    needs a one-bit word test;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.6**: Part 1, the resources and the cache, applies on every host; the cache is fetched
    for your brief's Mathlib roots only), and the copy-text screen v3
    `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/eq/inputs/eq-fill-query-cont1/`): the import probe, the
    route probe with its seal controls, the semantic-duplication probe, the review's route lemmas
    with their controls and duplication probe, and the screen population; the order list
    `campaign/fills/eq/orders/eq-fill-query-cont1.txt`, the base sorry set, the screen base and the
    pre-ship log (`campaign/fills/eq/logs/eq-fill-query-cont1-*`). The route's design note is
    `campaign/items/c1/c1e/EQ-route-design.md`.
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule
  (E-RES). Fetch the cache for your roots only (34); never run the unfiltered
  `lake exe cache get`. If Lean cannot start, follow Part 2 exactly. **If Lean never runs, do not
  draft proofs blind**: deliver the environment report only.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/eq-query-cont1 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
  # must print f965eac02e06549e8239c7476b31c0ced4f3d11b
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-eq-query-cont1.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - **the environment logs** (`evidence/logs/` at the clone's root: preflight,
    cache store, roots, cache fetch, manifest check), this item's bootstrap and final sweep logs
    with **each module's time and maximum memory**, and the axiom log;
  - the seal test's source, its controls and both outputs; both screen outputs; and
    `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write `fill-eq-query-cont1-cp<N>.zip`
  (`N` the checkpoint's number, 2 to 7) with the same contents as of that commit (the final sweep
  may be your module's check only). Deliver the latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign's tree after checkpoint 1's landing (PR #173)**
  (@ANCESTOR@ adds records only). Lines in this brief are those of your base's tree, where
  `NTimeDiagonalizer.lean` is 498 lines (22 public, 3 private, and their compiler auxiliaries).
- **There is no overlay.** The file already has its nine imports; your first edit is a proof edit.
  Where the line numbers below differ from the first round's brief, these are the base's.
- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩. Cite nothing they add.

## Parallel batches this round

None in `NTimeDiagonalizer.lean`. **E-D** (`Turing.NTimeDiag.exists_diagonalizer`, the same file)
follows this item, citing your target's statement only. `ntime_hierarchy` (`NTimeHierarchy`) is
proved from `exists_diagonalizer`'s statement by a separate maintainer PR (#172), which imports
your file; your target's statement is frozen, so it is unaffected.

## What this is

**The stage query of the lazy diagonalizer** ([AB09, §3.2, proof of Theorem 3.2 and Figure 3.1];
[Coo72]): one deterministic machine computes `Turing.NTimeDiag.query f g` within `C · (g n + 1)`.
The statement and its docstring are **frozen verbatim** (lines 248–273: the docstring 248–269;
the statement):

```lean
theorem exists_queryTM {f g : ℕ → ℕ} (hf : Complexity.TimeConstructible f)
    (hg : Complexity.TimeConstructible g) :
    ∃ (G : FinTM Bool) (C : ℕ), G.ComputesFunInTime (query f g) fun n => C * (g n + 1) := by
  sorry
```

Its docstring's sketch binds where this brief does not refine it. **This brief refines it in two
places, by the maintainer's route note** (`EQ-route-design.md`, ruled by the user 2026-10-25):
- **the arithmetic is unary with cutoffs**, not "fixed-degree binary arithmetic": no multiplication
  leaf;
- **`f`'s witness runs through a clocked install call**, so each round's scratch is restored by the
  call itself.

Propose an `**Implementation.**` paragraph for the maintainer (`REPORT.md`); the docstring stays
frozen.

**Where it stands.** Checkpoint 1 is landed: the target's body is `qy_query_of_main` applied to
the main machine's contract, under a `suffices`, and what is open is exactly

```lean
∃ (M : FinTM Bool) (A : ℕ),
  M.ComputesFunInTime (fun x => query f g (List.replicate x.length true))
    (fun n => A * (g n + 1))
```

(`hmain`), on **every** word: `[]` when `|x| ≤ 2` (`query_of_not_guard`), and `query_eq`'s word
when `|x| ≥ 3`. `g`'s witness from `timeConstructible_iff` computes `bits (g |x|)` on every word,
so the input call on the native input serves non-unary words too; `n ≤ g n` is already
absorbed by `qy_query_of_main`.

**Proved modulo, exactly:** none. **A complete delivery has no `sorryAx` in the target.**

**Read first:**
- the target's docstring, and `query`'s and `stage`'s;
- the route note `campaign/items/c1/c1e/EQ-route-design.md`;
- the route probe `EQRouteProbe.lean.txt` (below): its sealed lemmas may be copied into your home
  as `qy_` privates;
- `exists_stepClockTMVia`, `exists_installCallTM`, `exists_inputCallTM`, `computesFunInTime_cond`,
  `Round.iterate_seq` with `Round`/`round_iff`, `expandTM_run_ofCfg`, `copyMapTM_run_ofCfg`,
  `writeAdvTM_run_ofCfg`;
- the release adapter `seamReleaseTM_runFrom_pos`, the input seek `exists_inputSeekTM`, and
  `exists_inputCallTM`'s proof (its split on `entry = exit`): a call's exit may be its entry.

**Pre-ship check** (the maintainer, on the landed tree against its replay snapshot; its log is
`campaign/fills/eq/logs/eq-fill-query-cont1-preship.log`):
- **The base file** elaborates with exactly its two sorry warnings (lines 402 and 472), and the
  three landed privates are within the standard three axioms. Every probe below reproduces the
  first round's output exactly on this tree.
- **The import probe** (`EQImportProbe.lean.txt`, **182 checks of 182 names**: megafill D's
  76 after dropping the virtual-input host's five, the route's 43 more, `timeConstructible_iff`
  and `Round.iterate_seq`, and 61 for the release adapter, the input seek, the scan, fold and
  emitter rows, `BufferWords` and the layout equations): 0 errors, 0 warnings. **Re-run it after
  your delivery**, extended by every further name you cite.
- **The route probe** (`EQRouteProbe.lean.txt`, 16 lemmas, 14 of them axiom-printed, and the
  decision `qyDecide` over `QyStep`), sealed over 7 TCSlib definitions
  (`TimeConstructible`, `ComputesInTime`, `ComputesFunInTime`, `MultiTapeTM.runFrom`,
  `MultiTapeTM.initCfg`, `counterValue`, `pairEncode`): 0 diagnostics, each lemma within the
  standard three axioms. It carries megafill D's dossier lemmas, with A1's
  `timeConstructible_iff` now cited, not stood in:
  - `qy_witness`: the elimination;
  - `qy_decide_spec`, `qy_stage_of_stop`: the stop rule;
  - `qy_round_le`, `qy_ledger`: the passed-rung bound and the ledger.

  It adds the note's new steps:
  - `qy_guard`: the guard split's equation. **It is landed**, with the same statement, as the
    file's private `qy_guard` (checkpoint 1): cite that one, and do not copy the probe's (the name
    would clash, and the copy would be a second proof);
  - `qy_ones_val`, `qy_rung_val`: the all-ones counter's value `2^m − 1` and the next rung's
    counter value `2^m`;
  - `qy_ones_ge`, `qy_two_pow_bits_le`: the counter is at least `D (n + 1)` and its width's
    power at most `2n + 1`;
  - `qy_log_bits`: `⌊log₂ n⌋ = |bits n| − 1`;
  - `qy_pow_two_bits`: the power-of-two test on `bits n`;
  - `qy_call_bound`: the install call's bound under `f a ≤ n`, the timeout certificate's
    arithmetic;
  - `qy_stage_lt_log` (with `qy_two_pow_le_ladder`): `stage f n < log₂ n`.

  Its docstrings are probe records: `qy_ladder_succ_eq` has none, and two name campaign items
  ("A1's reading", "the dossier's `eqDecide`"). Give every declaration you copy a public-facing
  docstring.
- **The seal controls** (`EQSealControl.lean.txt`, 7 `rfl` goals, one per sealed definition):
  every one closes unsealed and fails sealed.
- **The semantic-duplication probe** (`EQDupProbe.lean.txt`): the route probe's statements, each
  posed to `exact?` against your module's closure with the file's imports: all ten new ones
  "could not close" (megafill D's probe covered the dossier's five).
- **The review's route lemmas** (`EQReviewProbe.lean.txt`, sealed over 12: the route probe's 7 and
  `Cfg.ofWords`, `stateWord`, `Cfg.mapState`, `seamReleaseTM`, `Cfg.Stopped`; their 5 further
  controls in `EQReviewSealControl.lean.txt`, each failing sealed): 0 diagnostics, the standard
  three. They may be copied into your home as `qy_` privates, with public-facing docstrings:
  - `rv_release_first_stop`: a call released at its entry first stops at `Sum.inr exit` exactly
    at the call's exit time, whether or not `entry = exit`;
  - `rv_call_output_nil`: a timed-out call has emitted nothing;
  - `rv_seek_home`: the input seek at `p = 1` brings the input head home from anywhere;
  - `rv_query_word` (with `rv_flatMap_dbl_dbl`): the query word's shape;
  - `rv_X_cells`, `rv_cube_le`: the round's cell count and the ledger's cube bound.

  Their duplication probe (`EQReviewDupProbe.lean.txt`): 3 of 4 "could not close"; the fourth,
  doubling twice, is Mathlib's `List.flatMap_assoc` (cite it).

## Owned regions and targets (modify these and nothing else)

| # | File:line (base) | Target |
|---|---|---|
| 1 | `NTimeDiagonalizer.lean:402` | `Turing.NTimeDiag.exists_queryTM` (frozen statement) |

Your regions:
- **(a) no import.** The nine are in the file (the first round's eight and `Build/WordTests`); add
  none.
- **(b) your home**, the blank line after `qy_query_of_main` (line 375), before the target's
  docstring: your `private` declarations. **The three landed privates are frozen** (`qy_guard`,
  `qy_guard_decider`, `qy_query_of_main`): change none without stopping on that item and
  reporting it.
- **(c) the body**, the `sorry` under the `suffices` on line 410: prove `hmain`.
- **(d) the `**Implementation status.**` paragraph** at the end of the target's docstring (line
  399): update it to what is proved and what is open. It is public-facing library text: no
  campaign labels, no dates, no session narrative. The same holds for your new docstrings;
  provenance goes in `REPORT.md`. **Every new declaration has a docstring, and every proof over 20
  lines a literal `**Proof sketch.**` paragraph** (`policy.md` §3).

In (b): `private` only, and no `section`, `open` or `variable` that leaks past one (`open … in` on
one declaration is fine). Frozen: the module header (lines 14–69: the maintainer updates its
status at integration), every definition and law, the target's statement and docstring before
(d), **`exists_diagonalizer` and its docstring (E-D's region, 275 to the end)**, and every other
file.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The clock:** `Turing.exists_stepClockTMVia` (or its `Bool` instance `exists_stepClockTM`).
  **Never write a second clock, counter or countdown.**
- **`f`'s witness: through its install call.** Take `M_f` from `hf` by
  `Complexity.timeConstructible_iff` (never by unfolding `TimeConstructible`; read
  `ComputesFunInTime` through `FinTM.computesFunInTime_iff`). Then `C_f` comes from
  `FinTM.exists_installCallTM M_f (fun y => Nat.bits (f y.length)) (fun m => c_f * (f m + 1))`.
  **Its `entry` and `exit` may coincide** (the statement quantifies them separately), so run
  `C_f` released at its entry: `seamReleaseTM C_f.tm entry` from the fresh state `Sum.inl ()`,
  which at every positive time is `C_f`'s run right-tagged (`seamReleaseTM_runFrom_pos`), under
  the clock with the stop state `Sum.inr exit`. **Never run the witness through `vhostSilentTM`
  or a hand-built bank:** a passed round would leave its work tapes dirty, and only the install
  call's tracked banks restore them.
- **Every call you sequence** (install or input; a seam and the phase host dispatch at an exit
  before its action): release it at its entry the same way, or split on `entry = exit` as
  `exists_inputCallTM`'s proof does.
- **`g`'s witness and every unary-to-binary conversion: through the calls.**
  - `bits (g n)`: `FinTM.exists_inputCallTM` of `g`'s witness, on the native input.
  - `bits n` at the setup: `exists_inputCallTM` of `computesFunInTime_lengthBits`.
  - `bits (|w|)` of a tape-resident unary word `w` (`j + 1`, `X²`): `exists_installCallTM` of
    `computesFunInTime_lengthBits`.
- **Unary from binary:** `expandTM_run_ofCfg` (pattern `[true]`, the counter's value through
  `counterValue_bits`/`counterValue_eq`). **No second expansion loop.**
- **The guard split:** `FinTM.computesFunInTime_cond` with `computesFunInTime_const []`.
- **Compose by the public combinators:**
  - the R2 seams (`seamCompTM`, `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`,
    `seamCompTM_runFrom_left`/`_right`) and the phase host (`phaseHostTM`, `phaseHostTM_run`,
    `phaseHostTM_run_le`);
  - R1 (`embedEmitTM`/`embedSilentTM` and their run and visited lemmas);
  - the contract layer: `Contract.ofSegment`, `seq`, `inPhase`, `branch`, `segment`,
    `Segment.trans`/`mono`/`take`, and `Round`, `round_iff`, `Round.segment`, `Round.iterate_seq`;
  - the framed catalog rows `copyMapTM`, `clearTM`, `skipTM`, `skipBackTM`, `rewindTM`,
    `writeAdvTM` (their `_run_ofCfg`/`_contract` forms).
- **Leaves you may write** (each private, a finite-state scan or a fixed composition of the rows
  above, with a docstring saying which public row it is not):
  - **L1, the guard decider**: `x ↦ [decide (x = replicate |x| true ∧ 3 ≤ |x|)]`, linear time,
    composed from the framed input fold `Turing.inputFoldTM` (`inputFoldTM_run_ofCfg`) and a
    verdict emission over `Turing.emitAction` (`FinTM.emit_halts`), or from the function-level
    rows (`computesFunInTime_incFixed` with `incFixed_eq_none_iff_replicate`,
    `computesFunInTime_ifEq`, `computesFunInTime_cond`): not a hand-written scan of the input.
  - **L2, the binary `≤`** of two tape-resident `Nat.bits` words (lengths first, in lockstep, then
    from the top bit; `Nat.bits` has no trailing `false`), **within a constant times
    `|bits n| + 1` steps whatever `|bits (f a)|` is**: no published lemma bounds `|bits (f a)|`
    by the call's time.
  - **L3, the unary compare and the cutoff product**: compare two unary words, and write
    `1^{min (u·v) K}` from unary `u`, `v` and a unary cutoff `K`, within
    `O((u + v + K + 1)²)` steps.
  - **L4 is not a leaf.** The power-of-two test (`bits n = replicate L false ++ [true]`) and the
    setup's `n ≥ 3` test are folds over `bits n`: the fold instance of the framed scan
    `Turing.scanTM` (`scanTM_run_ofCfg` or `scanTM_contract`, with `scanFold` and `scanKeep`;
    `scanResult_fold`: the verdict `done (w.foldl δ a₀)` at exactly `2|w| + 2`, the word intact).
  - **L5, the unary `Nat.unpair`**: `(Nat.unpair h).1` in unary from `h` in unary (`h < log₂ n`),
    within `O((h + 1)³)` steps, composed from L3 and the rows above.
  - **L6, the writer's emitter**: emit a tape word with each bit written `r ∈ {1, 2, 4}` times,
    optionally omitting its last symbol (for `α = (bits (j + 1)).dropLast`); fixed words over
    `Turing.emitAction` (`FinTM.emit_halts`, `FinTM.emit_run`).

  L2 and L3 say in their docstrings why `compareTM_contract` (equality, at `compareStop`) and
  `walkTM_run_ofCfg` (the lockstep ruler) do not serve. **Any further leaf is an escalation.**
- **The input head after a timeout.** Every call starts at `Cfg.ofWords`, with the input head at
  `1`. After the clock's timeout the input head is the call's at some time before its exit, which
  no published clause determines, and the call's bank and the counter tape are dirty. So, after
  the loop and before any call, return the input head to `1` by the input seek
  `Turing.exists_inputSeekTM` at `p = 1` (`Build/InputCall`), on two dedicated tapes written at
  the setup (`[true]` and a blank one), within `C (1 + pos + 2) ≤ C (n + 4)` steps. A timed-out
  call is silent: its output is a prefix (`MultiTapeTM.output_prefix`) of its exit's, which is
  `[]`. No later phase touches the call's bank or the counter. Never write an input rewind;
  `Turing.inputRewindTM` is outside your imports and needs the head at `1` or more.
- **Promotion candidates** (notes only, in `REPORT.md`): the clocked install call ("run a
  function-level machine on a tape word with a cap, scratch restored"), L2, L3 and L6.

### The route (binding where it names a row)

Write `n = |x|`. From `hf` and `hg` by `timeConstructible_iff`: `n ≤ f n` and `n ≤ g n` for all `n`;
witnesses `M_f`, `M_g` with constants `c_f`, `c_g > 0`. `L = ⌊log₂ n⌋ = |bits n| − 1`
(`qy_log_bits`).

**The guard** (checkpoint 1, **landed**). `G` is `computesFunInTime_cond` of L1
(`qy_guard_decider`), `M₁`, and `const []`, by `qy_guard` and `qy_query_of_main`. `M₁` reads only
`|x|`, and must halt within its bound on **every** `x`, including `n ≤ 2`: its setup tests
`n ≥ 3` on `bits n` (the scan fold) and outputs `[]` otherwise, which is `F x` there.

**`M₁`'s setup** (checkpoint 2). `bits n` by the input call, then:
- `L` in unary (`copyMapTM` mapping to `true`, one cell erased);
- the rung `ℓ₀ = 2` and the stage index `h = 0` in unary;
- the input seek's two tapes (`[true]`, and a blank one);
- the clock's counter: the all-ones word of width `m = |bits n| + |bits D₀|`, of value
  `2^m − 1 ≥ D₀ (n + 1)` (`qy_ones_val`, `qy_ones_ge`). `D₀` is a constant such that, whenever
  `f a ≤ n` and `a ≤ n`, `C_f` returns within `D₀ (n + 1)`, by its bound
  `c' (c_f (f a + 1) + a + |bits (f a)| + 1)` and `|bits (f a)| ≤ f a`
  (`Turing.length_bits_le_self`): `D₀ = c' (c_f + 2)` (`qy_call_bound`). Write it by `copyMapTM`
  from `bits n` (every symbol mapped to `true`), then `writeAdvTM` of the fixed word
  `replicate |bits D₀| true`, its head back at the word's start.

Every phase cost is `O(n)`.

**One round at the rung `ℓ < n`, `a = ℓ + 1`** (checkpoint 3; state it as a `Turing.Round` at the
locator's anchor, with three escapes: interior, top, timeout).
1. Install `1^a` on `C_f`'s tape `0` (a copy of the rung, one more cell). Run `C_f`, released at
   its entry, under the clock (stop state `Sum.inr exit`).
   - **Timeout** (no return within `2^m − 1`): `n < f a` by the call's bound (`qy_call_bound`). The
     escape is interior; the input head is then unknown and the call's bank dirty (the input
     seek, above).
   - **Finish:** `bits (f a)` on `C_f`'s tape `0`, every other tape of the call blank, the input
     head at `1`. The clock leaves "some word of the same width" on all `m` counter cells:
     rewrite the whole width every round (`copyMapTM` from `bits n` and the fixed tail again).
2. `n < f a`? by L2 on `bits (f a)` and `bits n`. Yes: interior.
3. `X = f a + a + 1` in unary: `expandTM` with the counter `bits (f a)`, then one copy of the rung
   and two cells (`X = f a + ℓ + 2`).
4. `X > L`? by L3: interior. Otherwise `X⁴` against `L` by L3's cutoff product with `K = L + 2`,
   twice. Then decide by `qy_decide_spec`'s three cases:
   - `X⁴ < L`, or `X⁴ = L` with `n` not a power of two (the scan fold, `qy_pow_two_bits`): **next**;
   - `X⁴ = L` with `n` a power of two: **top**, keeping `X²` (the budget) in unary;
   - otherwise: **interior**.
5. **Next:** write the counter `replicate (X⁴) false ++ [true]` (value `2^{X⁴}`, `qy_rung_val`)
   and expand it to the new rung `ℓ' = ladder f (h + 1) < n` in unary (`qy_ladder_succ_eq`'s
   form). Increment `h`, clear the round's scratch (`clearTM`, rewinds), and return to the
   anchor.

The round's cost: a passed round is `O(ℓ_{h+1} + (L + 1)²)` (`qy_round_le`); the stopping round
is `O(n + (L + 1)²)`.

**The loop** (checkpoint 4). The passed rounds form a sequence of configurations at the anchor;
`Round.iterate_seq` gives their segment over the summed time. Append the stopping round by
`Round.segment` and `Segment.trans`. At its escape:
- `h = stage f n` and `ℓ = ladder f h`, by `qy_stage_of_stop` and induction on the passed rounds
  (each advances to `ladder f (h + 1)`);
- the escape says whether `n` is the top.

The ledger: `∑_{h < s} ℓ_{h+1} ≤ 2ℓ_s < 2n` (`qy_ledger`), plus `s · O((L + 1)²)` with
`s < log₂ n` (`qy_stage_lt_log`), plus the last round's `O(n)`. All of it is `O(n)`; state it as
`≤ A (n + 1)` for a constant `A`. The polylogarithmic terms (this one and L5's `O((L + 1)³)`) are
linear by `(L + 1)³ ≤ 8 · 2^L` (a private arithmetic lemma) and `2^L ≤ n` (`Nat.pow_log_le_self`).

**After the loop** (checkpoints 5 and 6).
- **The input head:** the input seek at `p = 1` (above), `O(n)`.
- **The stage code:** `j = (Nat.unpair h).1` by L5, `bits (j + 1)` by the install call of
  `computesFunInTime_lengthBits` on `1^{j+1}`, and `α = (bits (j + 1)).dropLast`
  (`stageCode_eq`). Cost `O(n)`.
- **The budget field:**
  - **middle:** `bits (g n)` by `exists_inputCallTM` of `M_g`, cost `O(g n + 1)` (with `n ≤ g n`);
  - **top:** `bits (X²)` by the install call of `computesFunInTime_lengthBits` on `1^{X²}`, where
    `X² = budget f ℓ` (`budget_eq`).
- **The writer** (L6). The outer pairing doubles the whole inner pair, its separator included:
  `pairEncode (pairEncode B α) t` is `B.flatMap (fun b => [b, b, b, b])`, then
  `[false, false, true, true]`, then `α.flatMap (fun b => [b, b])`, then `[false, true] ++ t`
  (`pairEncode_eq` twice, `List.flatMap_append`, `List.flatMap_assoc`). Emit, in order:
  - the flag (`true` at the top, `false` in the middle);
  - the budget field's bits, each written four times;
  - `[false, false, true, true]`;
  - `α` doubled;
  - `[false, true]`;
  - the tail: `1^{ℓ+1}` at the top, from the rung; `1^{n+1}` in the middle, from the input length
    in unary (`expandTM` on `bits n`, then one cell).

  This is exactly `query_eq`'s word. Cost
  `O(|bits (g n)| + |α| + n + 1) = O(g n + 1)`.

**`M₁` and the target** (checkpoint 7). Assemble `M₁` by seams and the phase host, halting after the
writer, and silent before it. Its time is `≤ A' (g n + 1)`. Then `computesFunInTime_cond` and
`qy_guard` give the target, with `C` read off the conditional's bound
`c (T₀ n + max (T₁ n) (T₂ n) + 1)` and `n ≤ g n`.

**Edge cases that must stay true:**
- `n ≤ 2` (the setup's short-circuit) and `n = 3`;
- a top `n = ladder f (i + 1)` and the first stage `i = 0`;
- `f a > n` reached by a timeout (then the input seek, and a silent dirty bank), and by a fast
  witness with a large output (L2's bound);
- `X > L`, and `X⁴ = L` with `n` not a power of two (advance);
- `g n = n`, the smallest allowed.

## Gate guidance (binding)

- **Gate 39** (the statement gate, round 2): `query` is defined mathematically, so the timeout
  reasoning stays inside this fill. The bound is `C · (g n + 1)` with no other term; `C` is
  uniform (no dependence on `x`).
- **The C1-E design** (`campaign/items/c1/c1e/C1E-design.md`, "Deviations"): one machine computes
  the pure function (D1, D2, D4, D5 internal), and its arithmetic rows are private leaves with
  promotion requests. This brief's leaves (L1–L3, L5, L6) and the scan folds are those rows, in
  unary where the note says so.

## Cited infrastructure (public and proved at the issue commit; all in `EQImportProbe.lean.txt`)

The probe's 182 names: the target and the stages' laws; A1's reading and the function-level API;
the calls, the release adapter and the input seek; the clock; the expansion, copy, clear, skip,
write, rewind, scan, fold, compare and walk rows and the emitter; the seams, the phase host, R1,
the layout equations and the contract layer; `BufferWords`; `Nat.bits`, `Nat.log` and
`Nat.unpair` facts.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `NTimeDiagonalizer.lean`. List every
   new declaration with its role.
2. **Statement freeze** over the target and every landed public declaration.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. Checkpoints 5 and 6 depend on 4's escape, not on its ledger.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly the nine in region (a).
7. **One proof per shared argument.** Never write a second clock, counter, expansion, call,
   seam, embedding, round loop or input rewind. Never re-walk `ExhaustiveReplay`'s `xr_`
   privates (its capped replay, window clear and translation), `TimeHierarchy/ClockLoop`'s, or
   `Build/Loop`'s call machinery (`callTM`, `emCall_*`). L1–L6 are allowed.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 361 lines; 22 public, 0 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch") and the target's axiom walk. A partial is expected and
   fine; an unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own definitions and privates.
    - **Never unfold a definition of another file**, and no definitional closure either.
      - `TimeConstructible`: only through `timeConstructible_iff`.
      - `ComputesFunInTime`/`ComputesInTime`: through `computesFunInTime_iff`/
        `computesInTime_iff`.
      - The clock's layout: through `clockCfg_*`.
      - `counterLoopCfg`: through `Turing.counter_cfg_eq` (the body bank, then the counter) and
        `counterLoopCfg_body`; it has no per-field equations.
      - A released call: through `seamReleaseTM_runFrom_pos`.
      - `pairEncode`: through `pairEncode_eq`.
      - `Cfg.ofWords`/`stateWord`: through their equations.
      - A machine's initial state: through the `with q₀` override's two equations.
    - **Scope (user, 2026-10-23):** this binds TCSlib's own definitions. Core and Mathlib
      definitions may reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`,
      `rw` or `unfold`; use their equation lemmas (`Nat.bits_append_bit`, `Nat.log` lemmas,
      `Nat.unpair` lemmas).
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their lemmas. Unfold `step` and `Action.apply` only for a
      leaf defined in your own file (L1–L6).
    - Your own file's definitions (`ladder`, `budget`, `stage`, `stageCode`, `query`) may be
      unfolded, but prefer their laws.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check by both methods** (neither alone is complete):
      - a **seal test**: a scratch copy of your module with `attribute [local irreducible]` on
        every other-file TCSlib definition your proofs mention. Start from the pre-ship's 7 and
        extend: at least `Complexity.TimeConstructible`, `FinTM.ComputesFunInTime`,
        `FinTM.ComputesInTime`, `MultiTapeTM.runFrom`, `MultiTapeTM.initCfg`, `Cfg.ofWords`,
        `stateWord`, `clockCfg`, `counterLoopCfg`, `expandTM`, `copyMapTM`, `seamCompTM`,
        `embedEmitTM`, `embedSilentTM`, `pairEncode`, `seamReleaseTM`, `phaseHostTM`,
        `Cfg.mapState`, `Cfg.Stopped`, `embedEmitCfg`, `FinTM.bufferTape`, `scanTM`, `inputFoldTM`,
        `writeAdvTM`, `clearTM`, `rewindTM`, `dbl`. Add `attribute [-simp]` on the `@[simp]`
        definitions among them. A reducible `abbrev` (`Cfg.Halted`, `counterLoopOrbit`) cannot be
        sealed: read it through its body (`policy.md`). The copy must still elaborate, **with
        controls**: for each sealed
        definition, a goal that closes by `rfl` with nothing sealed and fails under the seal;
      - an **inspection table** of every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change`
        argument in your diff, each other-file name classified (a theorem, or a definition: a
        finding).
      - **Ship the raw outputs** of the seal and its controls, with their commands and exit
        statuses. **A seal not run, or a seal without controls that fail sealed and close
        unsealed, is a checklist failure.**
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`); use the framed `_ofCfg` forms. Cite no private declaration of
    another file. Keep your new privates under the `qy_` prefix (`Qy`/`qy` for types and
    definitions, as `QyStep`, `qyDecide`; unused in the tree at the drafting base).

### Checkpoints (for a partial; ground rule 9)

1. **The guard** (landed).
2. **The setup** as a contract (the `n ≥ 3` scan, `bits n`, `L`, the rung, the seek's tapes, the
   counter), with its `O(n)` bound.
3. **One round** as a `Turing.Round` with its three escapes and its cost.
4. **The loop and its ledger:** the escape at `stage f n` with the top flag, within `A (n + 1)`.
5. **The input seek and the stage code:** the input head at `1`, then `α` on a tape.
6. **The budget field and the writer.**
7. **`M₁` and the target.**

Each may land alone. **Add no new admission:** a helper is inserted only once proved. The freeze
check for a partial is the axiom walk: `sorryAx` reaches the target only through its own open
body. **One checkpoint, one commit, one zip, delivered at once.**

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**). Run the before
screen right after branching, beside the bootstrap: it must equal the screen base. Run the after
screen once, at the end, beside the final sweep; checkpoint zips carry the tail check, the seal
and the axiom prints, not a screen.
**Run each screen on a frozen copy of its commit** (`git worktree add <dir> HEAD`, the screen's
root `<dir>`).
- **Semantic duplication (required).** The text screen misses a private that re-derives a lemma
  already published (gate 69: six prefix arguments re-deriving `Turing.phaseHostTM_run_le`; gate
  72: a private `(workReadsK 2).length = 9`). For **every** private lemma you add, search for a
  published declaration that states it or a generalization of it: in the tree and on every open
  PR branch, by name and by statement (`git grep`), and by an `exact?` or `apply?` probe on the
  statement. **Cite proved material; never re-prove it.** `REPORT.md` lists, for each new private,
  the search made and its result. The pre-ship probe `EQDupProbe.lean.txt` poses the route probe's
  statements: none is published.
- **The population** is 30 files
  (`campaign/fills/eq/inputs/eq-fill-query-cont1/screen-population.txt`):
  - your file;
  - the files the route cites: `Build/StepClock`, `Build/Loop`, `Build/InputCall`,
    `Build/Wrappers`, `Build/Primitives`, `Build/CounterLoop`, `Build/Scan`, `Build/Catalog`,
    `Build/Rewind`, `Build/Seam`, `Build/Embed`, `Build/Contract/Basic`,
    `Build/Contract/Catalog`, `Build/Contract/Seam`, `Build/Convention`, `Composition`, `Finite`,
    `Encoding`, `StateRenaming`, `BufferWords`, `ClassP/TimeConstructible`, and `Build/WordTests`
    (the guard's rows);
  - the known hazards: `ClassNP/ExhaustiveReplay` (capped replays over the same clock),
    `TimeHierarchy/ClockLoop` (a colleague's clocked loop), `Diagonalization/NTimeHierarchy`,
    `Simulation` (the input-rewind and emitter family), `Build/SeamLayout` (a phase-host composite
    over catalog rows and private leaves: a model to read, not to copy), and `ClassNP/TMSAT` and
    `ClassNP/Nondeterminism` (private unary deciders, L1's neighbours).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/eq/logs/eq-fill-query-cont1-screen-base.txt`: **1,735
  declarations, 2,152 pairs, 757,579 characters** (MEASURED at your base; about 19 minutes under
  `nice -n 10`, peak memory 2.0 GB).

```sh
P=campaign/fills/eq/inputs/eq-fill-query-cont1
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **A new cross-file pair** with an owned-file declaration on one side is listed in `REPORT.md`
  with its shared tiles and one disposition:
  - **idiom**: the shared text is a public row's invocation and the standard conversion around it
    (for example `FinTM.computesFunInTime_ifEq w [true] [false]` with `convert … using 1;
    funext x; by_cases hx : x = w <;> simp …`), and no lemma, public or private, is re-derived.
    Justify it in one line and go on;
  - **re-derivation of a published lemma**: cite the lemma instead, before the zip;
  - **re-derivation of another file's private**: keep yours, and list it as a promotion request.

  **None of these ends the item.**
- **Your file has no pair in the screen base.** The first round's two guard pairs (with
  `a3n_poly_fixed_eq` and `tmsat_pt_eq`) are gone: since #171 all three cite the published word
  tests. The `Cfg.mapState_mapState` field-equation idiom stays an accepted idiom pair elsewhere.
- **Known hazards:**
  - `ExhaustiveReplay`'s `xr_replay_finish`/`_timeout` (the clock's two exits, read the same way):
    cite `exists_stepClockTMVia`'s two clauses, never a prelude copied from them;
  - the calls' internals (`Build/Loop`'s `emCall_*`): cite the call contracts;
  - `Build/Catalog`'s scans and `f2_` privates, against L1–L4: cite a framed row wherever one
    exists;
  - the `Cfg.mapState_mapState` field-equation idiom (two accepted idiom pairs: say so if yours is
    a third);
  - `ClassP/BinaryArith` (#135, merged into `main`, not in your tree): its polynomial-time `le` and
    `lt` (`AddSub`) and unary `mulU` (`Loops`) are the nearest statements to L2 and L3. Ledger L2
    and L3 against them in `REPORT.md`, and include `origin/main` in the semantic search.

  A pair at 90% or more is a copy.
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only** (addendum v2.6, Part 1,
  items 2–4; your order list's modules import 34 roots directly);
  **never `lake build`**, and never the unfiltered `lake exe cache get`. Use
  `scripts/lean_check_tree.sh` for every check, one Lean process at a time.
- **E-SERIAL (megafill D) is not a deviation** (the user's ruling): the cache tool's own
  compilation inside `lake exe cache get` is outside the one-Lean rule. Do not stop, or open an
  escalation, for it or anything like it. Your own checks stay strictly one at a time: never two
  `lean_check_tree.sh` runs, probes or sweeps at once, and none while `lake exe cache get` runs.
  A screen may run beside one of them. **A process deviation never ends the item**: disclose it
  with its evidence and continue.
- **Budget, measured on the last fill host:** the fetch about 2 minutes; the bootstrap 8.2
  minutes; each screen about 19 minutes (1,159 s and 1,145 s); the final sweep 8.4 minutes; a
  tail re-check about 5 s. Reserve about 25 minutes for the finishing sequence (the final sweep
  with the after screen beside it, then the REPORT and the zip), and use the rest for proofs.
- **Bootstrap** (addendum Part 1, item 5) from
  `campaign/fills/eq/orders/eq-fill-query-cont1.txt` (**84 modules**), right after branching,
  logging each module's start and end time and maximum memory. **The base sorry-warning set has 21
  entries in 10 modules** (`campaign/fills/eq/logs/eq-fill-query-cont1-base-sorries.txt`). Yours
  are `NTimeDiagonalizer`'s two. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `NTimeDiagonalizer`: zero errors, exactly one sorry warning (`exists_diagonalizer`'s; for a
     partial, also the target's), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's.
  3. Re-run `EQImportProbe.lean.txt` (extended by your citations): 0 errors.
  4. **After every proof edit, the whole order list's tail from your module on**, not your
     module alone (megafill C's last edit needed a tail rebuild).
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended) for the target
  and every new private: within `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a
  complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL
  (base: 0 FAIL, 2 WARN over 5 files). No new line over 100 characters. Your file will pass 1000
  lines: the size WARN that follows is expected, not a failure (file size alone is not a driver).

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target: `exists_diagonalizer` (E-D, your file),
`ntime_hierarchy` (`NTimeHierarchy`), `exists_uniformSimulator` (`CodeSimulator`, B5a),
`exists_codeNDTM_accepts_linear` (`ClassNP/NDNormalForm`), and the older function-level and
space stubs of `Simulation`, `Composition`, `Encoding`, `ClassP/TimeConstructible`,
`Build/Wrappers`, `Build/Loop` and `Build/Primitives` (the list in
`campaign/fills/eq/logs/eq-fill-query-cont1-base-sorries.txt`). If a proof seems to
*need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] The preflight's numbers, the roots' count and the cache fetch's (quoted from the logs, the
      cache store's log included), **the logs copied into this zip**, the bootstrap with
      per-module time and memory, and the base blob check.
- [ ] No import added; the three landed privates unchanged; nothing outside regions (b)–(d).
- [ ] The checkpoints reached (2–7), **one zip each**; the base hash and the ancestor check.
- [ ] Every new declaration with its role; `M₁`'s tapes (the call's, the clock's counter, the
      rung, `L`, `h`, the seek's, the scratch); each leaf (L1–L3, L5, L6) and its run, and each
      scan fold.
- [ ] Each call's release (or its `entry = exit` split); the input seek after the loop; the
      timed-out call's silence.
- [ ] The base sorry list by name; each edge case with the lemma that covers it.
- [ ] `C`, term by term: the guard, the setup, the loop's ledger (passed rounds, the arithmetic
      term, the last round), the stage code, the budget field, the writer.
- [ ] Promotion candidates and escalations (each stated mathematically), or "none"; the proposed
      `**Implementation.**` paragraph for the maintainer.
- [ ] Rule 10: the declarations cited outside your file (from an elaborated-constant walk), the
      probe re-run as "N checks of M names", **the seal test with its controls and both raw
      outputs**, and the inspection table. Rule 11: a grep of your diff for the six R3 rows and for
      other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, the semantic search per private,
      "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line. The diff touches only your
      owned regions.

## Known pitfalls at this pin (hard-won)

- **From the first round:** each leaf's docstring says which public row it is not, and why. No
  core or Mathlib definition is reduced outside `rfl`, `decide` or `show`: write
  `congrArg (fun b => [b])`, not `congrArg List.singleton`. The seal erases all four `@[simp]`
  TCSlib definitions (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`) and seals
  every definition the walk reaches; recursive definitions (`incFixed`) get usage controls, not
  delta controls.

- **The install call's start is `Cfg.ofWords (input := x) entry (stateWord C.k arg)`**: every tape
  of the call blank except tape `0`, all heads at `0`, the input head at `1`, the output empty.
  Embed the call (R1) on tapes that are blank there, and read its endpoint through `Cfg.ofWords`'s
  equations.
- **The clock's stop state:** on the released call, with `stopAt s := decide (s = Sum.inr exit)`,
  a first stop at `τ` needs `∀ u < τ, ¬Stopped`: at `u = 0` the state is the fresh `Sum.inl ()`;
  at `0 < u < τ` it is the call's, right-tagged (`seamReleaseTM_runFrom_pos`,
  `Cfg.mapState_state`), off `exit` by the call's cut, and live since the call reaches `exit`
  (`MultiTapeTM.runFrom_state_ne_none_of_le`); read through `Cfg.stopped_iff`. **`entry ≠ exit`
  is not available**: neither call's statement excludes `entry = exit`. The clock's exits are the
  injective families `finish r` and `timeout r` over the body's state: route the whole timeout
  family through the phase host.
- **A seam's initial state has no equation:** use the `with q₀` override and
  `MultiTapeTM.initCfg_with_q₀`/`runFrom_with_q₀`. The phase host's is `phaseHostTM_q₀`, and a
  machine's initial configuration is the blank seam `Cfg.ofWords q₀ (fun _ => [])`
  (`initCfg_ofWords`).
- **`writeAdvTM` returns to its own anchor** (state `0`): a seam or the phase host would dispatch
  it at time `0`. Sequence it through `ReturnContract.release` (`seamReleaseTM`).
- **The round times are existential** (the calls' and the clock's `∃ t ≤ …`): choose them before
  `Round.iterate_seq`, whose `τ : ℕ → ℕ` comes first. The head relation can be
  `P := fun _ => True`: no space bound is needed.
- **The simps field equations are pointwise** (`Cfg.init_workTapes`, `clockCfg_workTapes`, …):
  `funext` before `rw`, or the step closes by unfolding and the seal rejects it.
- **`Nat.bits` is little-endian** with its top bit last: `bits (2^m) = replicate m false ++ [true]`,
  and `dropLast` removes the top bit.
- **`⌊log₂ n⌋` is `Nat.log 2 n`.** Relate it to `|bits n| − 1` once (`qy_log_bits`) and reason on
  lengths afterwards.
- **`computesFunInTime_cond` takes three machines computing on every input.** `M₁` must halt within
  its bound on non-unary and short inputs too: it reads only the length.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
