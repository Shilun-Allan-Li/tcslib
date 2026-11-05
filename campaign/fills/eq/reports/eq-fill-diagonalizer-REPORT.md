# E-D fill — `Turing.NTimeDiag.exists_diagonalizer` (complete)

**Delivery `fill-eq-diagonalizer.zip`.** Agent: Claude. Brief `eq-fill-diagonalizer.md`
(SHA-256 `959c45eceb37c7a676190d7cd09f1ea68d375d5ea956e99f618689f14554e20b`, verified).

**Outcome: complete.** The target is proved: `#print axioms Turing.NTimeDiag.exists_diagonalizer`
→ `[propext, Classical.choice, Quot.sound]`; no `sorryAx` (evidence/logs/axioms-final.log). The owned
file elaborates with 0 errors and 0 warnings (no sorry warning). Statements frozen; E-Q's text
untouched; no new admission; no new public declaration (the 106 new declarations are private, with
private hand-written instances, no `deriving`).

## Base, branch and delivery

- Clone of `https://github.com/Shilun-Allan-Li/tcslib`, branch `complexity/arora-barak-ch3-4`
  (tip `ed395375` at clone time). Ancestor check
  `git merge-base --is-ancestor c8b0711408c02a2c7e254663511ecdb65516ae88 HEAD`: **passed**.
- Work branch `fill/eq-diagonalizer` created at exactly
  `c8b0711408c02a2c7e254663511ecdb65516ae88` (`git rev-parse HEAD` printed it; the owned file's blob
  `852931eb9347377fcd2e4e3c1e754462b236c1ad`, as required). Never rebased, merged or
  cherry-picked. No push, no PR.
- Contents: `REPORT.md` (this file); `source/` (the full modified file); `patches/` (`git
  format-patch` series against the base, 11 commits: checkpoints 1–8 and three finishing commits);
  `fill-eq-diagonalizer.bundle` (`git bundle`, prerequisite the base only); `evidence/logs/`
  (environment, bootstrap, final sweep with each module's time and maximum memory, axioms, lint,
  per-checkpoint axiom walks); `evidence/seal/` (seal test source, its generator, controls, both
  outputs, summary); `evidence/screens/` (both v3 screen outputs, the population, the diff of new
  pairs); `evidence/dedup/` (semantic search); `evidence/probes/` (import probe extension, audit
  walk, `exact?` probe, cache probe); `evidence/runtime/` (the timing wrapper, the sweep and screen
  drivers); `SHA256SUMS`.

## Environment (addendum v2.6, Part 1)

- Preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1, limit 14,341,881,856 B, memory in
  use (usage − total_cache + total_shmem) 48,680,960 B, headroom 13.31 GiB; clone filesystem ext4,
  29.37 GiB free. **PASS** (floors 12 GiB, 4 GiB).
- Toolchain: elan installed, `leanprover/lean4:v4.25.0` (Lean 4.25.0, commit cdd38ac5). Lean starts
  normally; Part 2's shim was **not** used.
- Re-check before the cache: 26.96 GiB free (floor 8 GiB), PASS (`precache-recheck.log`).
- Cache store before the first fetch: did not exist (0 files) (`cache-store.log`).
- Roots: 34 (`mathlib-roots.txt`, identical to `campaign/fills/eq/orders/eq-fill-diagonalizer-roots.txt`),
  computed after the overlay. `TAR_OPTIONS=--no-same-owner lake exe cache get <34 roots>`:
  "Attempting to download 1003 file(s)", 1003 downloaded, "Decompressing 1003", exit 0, no failure
  (`cache-get.log`).
- Packages present match the manifest (11 OK; ABSENT: doc-gen4, UnicodeBasic, BibtexQuery,
  MD4Lean — no module of the order list imports them). Last line of `manifest-check.log`:
  `present=11 absent=4 (doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean) mismatches=0: PASS`.
- Zero-size oleans: 0. Cache probe (`import Mathlib.Algebra.BigOperators.Group.Finset.Basic`)
  elaborates (`cache-probe.log`).
- `/usr/bin/time` is absent on this host; `evidence/runtime/timed.py` logs each module's start/end,
  wall time and maximum RSS (`getrusage(RUSAGE_CHILDREN).ru_maxrss`, KiB) instead.
- Bootstrap: the whole order list (84 modules) in order, one process at a time
  (`evidence/runtime/sweep.sh`, `bootstrap.log`): 84/84 pass, 704 s in all, peak 2,997 MiB
  (`CodeSimulator`); the owned file (with the overlay) 46.9 s, 2,733 MiB. Sorry warnings: exactly the
  base set (19 declarations in 9 modules).


## Regions touched

`git diff -U0` against the base has exactly five hunks, all in the owned file (no other file of the
tree changed):
1. region (a): `+3` lines after `Build/WordTests` — exactly the overlay's three imports
   (`Build/NDHost`, `NDCodeSimulator`, `Build/VirtualInput`); the file equalled
   `NTimeDiagonalizerOverlay.lean.txt` before any other edit;
2. region (d): the module docstring's status line "(sorried; C1-E's second fill)" → "(proved)";
3. region (b) + (d): the 3,051-line block before the target's docstring (the new privates, in
   sections of their own, between `exists_queryTM`'s proof and `exists_diagonalizer`'s docstring),
   and the docstring's first two lines: "(C1-E; [AB09, proof of Theorem 3.2]; the route of C1's
   design §2.5 and the P3.3 gate's round 2, §§3–5)" → "([AB09, proof of Theorem 3.2 and Figure
   3.1]: the lazy diagonalization over the stages above)";
4. region (d): "(the statement gate, finding 1)" removed from the prefix-clause sentence;
5. region (c): the target's `sorry` → its body (22 lines).

E-Q's declarations and every statement (the target's included) are byte-identical to the base.

## The construction

`D = dzD κ = ⟨κ.K, _, guessRunTM (dzSet κ) (dzPexit κ) (κ.tp 6) (dzQ κ) ⟨.flag, none⟩ (dzAcc κ)
(dzRej κ)⟩` (`Turing.guessRunTM`, bundled as a `FinNDTM`), `κ : DzKit f g c BF` the kit
(`dz_kit_exists`). One guessed block of `m = g n + 1 + |bits (g n)|` cells on tape 6 (`dzBlk`):
the stream, one separator cell, the budget word. Halting by `guessRunTM_haltsWithin`, acceptance
by `guessRunTM_accepts_iff` (not the clean-setup `guessRunTM_silent_spec`). No `phaseHostND` is
composed by hand; no writer, handoff or acceptance lemma is re-proved.

### Tape plan (`DzKit.K = 14 + |qc| + |gc| + |pc| + |lc| + |ac| + kR + |BF|`)

Named tapes (`DzKit.tp i`, layouts `dzLay`): 0 the query (the query call's tape 0); 1 `bits (g n)`
(`g`'s call tape 0; consumed by the ruler's expansion); 2 `1^{n+1}` (the prepend call's tape 0);
3 the clock's counter `bits (g n)`; 4 the block's first expansion counter; 5 the separator's counter
`[true]`; 6 the block (the guess; the core's stream tape); 7 the ruler `1^{g n}`; 8 the query's tail
(the extractor call's tape 0; the decider's virtual-input buffer); 9 the budget word; 10 its
expansion `1^b`, then `bits b` (the `lengthBits` call's tape 0); 11 the core's input (capture tape of
the emissions; the core's virtual-input buffer); 12 the hosted capture tape (both simulators);
13 the decider's tape 0. Every call's other tapes, the core's tapes other than its stream, and the
decider's other tapes are in their own blocks from index 14 (`qyBank`, E-Q's same-file bank map),
never written by any other phase (`dz_bank_off`, `dzLay_off`), hence blank with heads at 0 whenever
used.

**Injections of the embedded machines.**
- Calls (`embedEmitTM` of `seamReleaseTM`, all released): query `κ.bQ` (tape 0 → 0), `g`'s witness
  `κ.bG` (→ 1), prepend `κ.bP` (→ 2), `lengthBits` `κ.bL` (→ 10), extractor `κ.bA` (→ 8).
- Expansions (`embedEmitTM (qyEmb2 dst ctr) (expandTM 1 0 [true])`): block `6 ← 4`, separator
  `6 ← 5`, ruler `7 ← 1`, budget `10 ← 9`.
- Emissions (`embedSilentTM (dzOne src) 11 (qyEmitTM 1 0 [] suf rr false)`): `src` = 10, 8, 2.
- The two clocked, hosted runs (`embedEmitTM σ H`, `σ = dzClkEmb buf cap ctr β`, `H` the step clock
  over `vhostSilentTM M`): the core `κ.sR` (buffer 11, `β = κ.bR` with the stream tape `jR ↦ 6`,
  capture 12, counter 3); the decider `κ.sB` (buffer 8, `β = κ.bB`, capture 12, counter 3).

### `P` (`dzSet`, 12 phases, `dz_setup`)

q (query input call) → g (`g`'s witness input call) → p (`[true] ++ x` input call) → c1 (copy
`bits (g n)` 1→3) → c2 (copy 1→4) → e1 (expand 4 into 6: `1^{g n}`) → w (`[true]` on 5) → e2
(expand 5 into 6: the separator) → cb (copy `bits (g n)` 1→6, appended) → rb (rewind 6) → e3
(expand 1 into 7: the ruler) → rr (rewind 7; its `done` is `pexit`). First exit at
`TP ≤ dzSetB κ G = (qcA + gcA + pcA + 40)(G + 1)`, uniform, the layout `dzSetL f g z`, every head
at 0, nothing emitted (`dz_setup_facts` gives `guessRunTM`'s block hypotheses).

### `Q` (`dzQ`, 23 phases, dispatch `dzQRed`)

1. **flag** `dzTakeTM` on tape 0: `none` → reject; `some true` → tt; `some false` → mt (`dz_flag`).
2. **tail** (mt / tt) `copyMapTM 0→8` from cell 1 (`dz_tail_run`, `copyMapTM_run_ofCfg` directly).
3. **middle preparation**: sb0 `skipBackTM 6` (0 → −1); walk `walkTM 7 {7, 6} pos` (tape 6's head
   lands on cell `G`); sep `dzTakeTM 6` (separator blanked); xfer `transferMapTM 6→9` (tape 6 is
   `bufferTape s₁`); sb1 `skipBackTM 6` (head 0) (`dz_split`); exp `expandTM` 9 into 10 (`1^b`);
   rwU; cmp `qyCmpTM 10 6`: `gt` → reject (`dz_test`); lb `lengthBits` call on 10 (`dz_norm`); al
   extractor call on 8 (`α`); e1/e2/e3 emissions onto 11 under `embedSilentTM`; rwZ rewind 11
   (`dz_rewrite`).
4. **middle run** runR: `embedEmitTM κ.sR κ.HR`; `finish (accept, _)` → accept; any other `finish`
   or `timeout` → reject (`dz_runR`).
5. **top run** runB: `embedEmitTM κ.sB κ.HB`; `finish` → rwK (rewind 12) → rd `dzTakeTM 12`:
   `some false` → accept, otherwise reject; `timeout` → reject (`dz_top_run`).
6. verdict phases acc / rej (`dzAcc`, `dzRej`, distinct: `dz_acc_ne_rej`).

`Q` is silent: both simulators are hosted silently (`vhostSilentTM`), the emissions are captured
(`embedSilentTM`), every other phase emits nothing; every segment lemma keeps the output `[]`.

**The clocked, hosted run is stated once** (`DzClockSpec`, `dz_clock_exists`), generic in the hosted
machine `M` and its stop predicate: the step clock `exists_stepClockTMVia` (identity digits) over
`vhostSilentTM M`, stopped on the hosted state's predicate, transported through `embedEmitTM` along
`dzClkEmb`. It is a composition of two registered hosts, not a new host, and a promotion
candidate. Both runs use it (`κ.cR` for the core with `stop q = (q = accept ∨ q = reject)`,
`κ.cB` for the decider with `stop = false`, i.e. its halt).

## `K`, term by term, and the per-code `C`

`K = dzK κ = (qcA + gcA + pcA + 40) + (qcA (7 acA + 8) + 2 lcA + 140) + 15`, uniform:
- `TP ≤ (qcA + gcA + pcA + 40)(G + 1)` (`dz_setup`: the three input calls' bounds
  `qcA (G + 1)`, `gcA (G + 1)`, `pcA (G + 1)`; copies `2|bits G| + 2`; expansions `2d + overhead
  ≤ 6G + 2|bits G| + 2`, `counterOverhead_le`; rewinds `G + 3`; one step per dispatch);
- `2m = 2(G + 1 + |bits G|) ≤ 4(G + 1)`;
- `T = dzQB κ G = (qcA (7 acA + 8) + 2 lcA + 140)(G + 1)` bounds every stream's run
  (`dz_qoff`: 2; `dz_qtop`: `2|tail| + 5 + 6G + 2|bits G| + 10`; `dz_qmid`: flag 2, tail
  `2|tail| + 3`, split `2G + 2|w| + 15`, test `9b + 2|w| + 12`, normalization `lcA (b + 1) + 1`,
  rewrite `acA (|tail| + 1) + 10|bits b| + 6|α| + 4n + 40`, core `5G + 2|bits G| + 3`; with
  `b ≤ 2G` (`dz_budget_le`, `qy_two_pow_bits_le`), `|tail| + 1 ≤ qcA (G + 1)` (`qcL`),
  `|α| ≤ acA (|tail| + 1)` (`acL`), `n ≤ G`);
- `+ 11 ≤ 11 (G + 1)`; so `TP + 2m + T + 11 ≤ K (G + 1)` (`dz_halts`, `dz_accepts_iff`).

Per code `α`: `C = max 1 (max C_R C_BF)`, `C_R` the core's total-time constant for `α`
(`κ.hR α`, from `exists_ndInterpreterCore`), `C_BF` `hBF`'s constant for `α`.
- Middle completeness: `C (t' + 1) ≤ g n` gives `C_R (t' + 1) ≤ g n` and, as `C ≥ 1`, `t' ≤ g n`.
- Top: `C_BF 2^{C_BF (T* + 1)} ≤ C 2^{C (T* + 1)} ≤ n ≤ g n` (`κ.hg`, from
  `timeConstructible_iff`).
The interpreter's prefix clause is not used.

## Edge cases

| Case | What happens | Lemma |
|---|---|---|
| `n ≤ 2`, non-unary input | the query is `[]`, the flag reads a blank: reject at time 2 | `dz_qoff` (`query_of_not_guard` via `query`'s cases in `dz_hQ`) |
| budget word above `g n` | `qyCmpTM`'s `gt`: reject | `dz_test` (the `else` branch), `dz_qmid` |
| `b = 0` | `1^0 = []`: the expansion writes nothing, `qyCmpTM` compares `[]`, `lengthBits` on `[]` gives `bits 0 = []` | `dz_test`, `dz_norm` (general in `b`) |
| stream shorter than an acceptance | the core rejects or the clock times out: reject | `dz_runR` (`if TR ≤ G ∧ v = accept`) |
| `BF` halts with a word other than `[false]`/`[true]` | the captured cell 0 is not `false`: reject | `dz_top_run` (`out.head? = some false` test) |
| clock `timeout` (either run) | reject | `dz_runR`, `dz_top_run` |
| `g n = 0` (only `n = 0`) | the block is the separator alone; ruler, `w_b`, counters empty; the walk moves one cell; allowance 0 | all lemmas are stated for arbitrary `G` (`dz_setup`, `dz_split` with `s₁ = []`, `dz_test`, `dz_runR`), and `dz_qoff` applies since `n = 0 ≤ 2` |
| any separator bit | `dzQRed .sep` sends every `some _` on | `dz_split` |
| every stream at a top | the same verdict (the decider reads only the tail) | `dz_qtop`, `dz_top_iff` |

## Calls and releases

Every call is run released (`seamReleaseTM` at its entry; `qy_callHost`), as E-Q's review F1
found necessary (a call's entry may equal its exit): the three input calls of `P` (query, `g`'s
witness, prepend) and the two install calls of `Q` (`lengthBits`, the extractor). The hosted
simulators are not calls; the clock stops them by its own stop predicate.

## E-Q's leaves cited (same-file privates), and where

`qyC` (every normal form), `qy_hosted` (every hosted phase), `qy_hosted_last` (`dz_setup`'s last
phase), `qy_guard_of_cut` (every guard), `qy_run_one` (`dz_take_run`), `qy_copy` (`dz_setup`),
`qy_rewind` (`dz_setup`, `dz_test`, `dz_rewrite`, `dz_top_run`), `qy_writeConst` (`dz_setup`),
`qy_expandHost` (`dz_setup`, `dz_test`), `qy_cmp_run`/`qyCmpTM`/`QyCmp` (`dz_test`, `dzQM`),
`qy_emit_run`/`qyEmitTM`/`QyEm`/`qyBody` (`dz_emit_run`, `dzQM`), `qy_writer_word` (`dz_core_word`),
`qy_callHost` (every call), `qy_embed_gen`, `qy_embed_state` (`dz_clock_exists`), `QyInSpec`,
`QySpec`, `QySpec.mono`, `qy_inputSpec`, `qy_installSpec` (`DzKit`, `dz_kit_exists`), `qy_arg_bank`
(`dz_arg_bank`), `qy_bits_val`, `qy_two_pow_bits_le`, `qy_bits_len_mono`, `qyBank`, `qyBank_zero`,
`qyBank_val`, `qyEmb2`. No E-Q leaf is copied: no second comparison, emitter, word lemma, call,
clock-of-a-call, expansion or rewind wrapper.

## The own leaf `dzTakeTM`

States `Option (Option Bool)` (`none` reading, `some o` holding the read symbol; existing types,
so no new inductive). From `none` it reads the cell under tape `i`'s head, writes a blank there
(`(some none, .pos)`), moves right, enters `some (w i)`. Its docstring names the missing row: "no
public row writes a blank at one cell (`Turing.writeConstTM` writes symbols, `Turing.clearTM` and
`Turing.transferMapTM` blank a whole delimited word)". Its step lemma `dz_take_run` is its own
(`qy_step` covers only steps that write nothing), proved by `MultiTapeTM.step_of_some` and the
`Action.apply_*` equations (`Action.apply_workTapes`), never by `show`/`change`/`rfl` on `step` or
`Action.apply`. It is used three times: the flag (tape 0), the separator (tape 6), the captured
bit (tape 12).

## New declarations (106, all private, under `dz`/`Dz`), with their roles

**The own leaf and glue.** `dzTakeTM` (the one-cell take, the brief's ruled own leaf),
`dz_take_run` (its step); `dz_silentCfg_eq` (the silent transport, reconstructed from its fields),
`dz_silent` (a captured run in normal form, `embedSilentTM`); `dzOne` (one tape as a bank).

**The clocked, hosted run (one lemma for both runs).** `dzClkEmb` and `dzClkEmb_eqs` (the clock's
tape map: buffer, hosted tapes, capture, counter, and its four equations), `DzClockSpec` (the clause),
`dz_clock_exists` (the step clock over `vhostSilentTM M`, generic in `M` and its stop predicate).

**The kit.** `dzAlpha` (the composite extractor's function), `dz_alpha_eq` (it returns `α` on the
middle's tail), `dz_out_le` (outputs of a function computed in time `T` have length `≤ T`),
`DzKit` (the calls with their clauses, the core with its clause, the two hosted clocks),
`dz_kit_exists`.

**The layout.** `DzKit.K`, `DzKit.le_K`, `DzKit.tp`, `DzKit.tp_val`, `DzKit.tp_ne` (14 named tapes);
`dzLay`, `dzLay_tp`, `dzLay_off`, `dzLay_update`, `dzLay_const` (tape and head layouts over the
named tapes); `dz_bank_off`; the banks `DzKit.bQ`, `bG`, `bP`, `bL`, `bA`, `bR`, `bB`;
`DzKit.bR_j`, `bR_off`, `bR_ne`, `bB_ne`; the hosted maps `DzKit.sR`, `DzKit.sB`; `dz_arg_bank`,
`dz_zero_bank` (a call's bank over a layout).

**`P`.** `DzPK` (+ private instances `dzPKDecEq`, `dzPKFintype`), `DzPPh` (+ `dzPPhFintype`,
`dzPPhDecEq`), `dzSetM`, `dzSetRed`, `dzSet`, `dzPexit`, `dzBlk`, `dzBlk_length`, `dzSetL`, `dzSetB`,
`dz_setup` (`P` as a contract), `dz_initCfg`, `dz_setup_facts`.

**`Q`.** `DzQK` (+ `dzQKDecEq`, `dzQKFintype`), `DzQPh` (+ `dzQPhFintype`, `dzQPhDecEq`), `dzQM`,
`dzAcc`, `dzRej`, `dzQRed` (the dispatch), `dzQ`, `dzQF`, `dz_notF`, `dz_acc_ne_rej`; `dz_handoff`,
`dz_flag`, `dz_tail_run`; `dz_split_tape`, `dz_split`, `dz_test`, `dz_norm`; `dz_core_word`,
`dz_emit_run`, `dz_rewrite`; `dz_runR`, `dz_top_run`; `dz_word_lt`,
`dz_budget_le`, `dz_padded_value`, `dzQB`, `dz_entry_vals`, `dz_cell0`, `dz_qoff`, `dz_qtop`,
`dz_qmid`.

**`D` and the contract.** `dzD`, `dzK`, `dz_split_stream`, `dz_hQ`, `dz_halts`, `dz_accepts_iff`,
`dz_first`, `dz_seg_read`, `dz_K_bound`, `dz_query_mid`, `dz_ones_succ`, `dz_mid_sound`, `dz_mid_complete`,
`dz_top_iff`.

Instances: the four phase-index instances are written as `private` (classical `DecidableEq`,
`Fintype.ofList`), so no public instance name is created (a `deriving` test at this toolchain
showed that `deriving` on a private inductive yields public `instDecidableEq…`/`instFintype…`
names). The phase carriers' instances `dzPPhFintype`, `dzPPhDecEq`, `dzQPhFintype`, `dzQPhDecEq`
are `private instance`s too.

## Promotion candidates

1. `DzClockSpec` / `dz_clock_exists` — the clocked, hosted run (step clock over `vhostSilentTM`,
   embedded); generic in the hosted machine and its stop predicate (the brief names it a candidate).
2. `dzTakeTM` / `dz_take_run` — a one-cell take-and-blank row; the catalog has no row writing a
   blank at one cell (a `Build/Catalog` row with an `_ofCfg` contract).
3. `dz_silentCfg_eq` — the reconstruction lemma of `embedSilentCfg` (the silent companion of the
   published `embedEmitCfg_eq`), for `Build/Embed`.
4. `dz_out_le` — a function computed in time `T` has outputs of length at most `T` (for `Finite`,
   next to `MultiTapeTM.output_length_le`).
5. `dz_word_lt`, `dz_padded_value`, `dz_budget_le` — a word's binary value is below `2^{|w|}`;
   zero padding keeps it (for `BufferWords` or `CounterLoop`).
6. **Promotion requests** (another file's privates the fill had to re-derive, kept per the brief):
   `Build/NDHost`'s `guessRun_split` (re-derived as `dz_split_stream`, screen 98%) and
   `ClassNP/ExhaustiveReplay`'s `xr_val_lt` (as `dz_word_lt`, 65%).

## Escalations

None. Every checkpoint (1–8) was reached and every item proved as stated.

## Proposed `**Implementation.**` paragraph (for the maintainer to land in the target's docstring)

> **Implementation.** `D` is `Turing.guessRunTM` over a deterministic setup and a deterministic
> run. The setup calls the stage query, `g`'s witness and `x ↦ true :: x` on the native input
> (released input calls), and writes the block `1^{g n} ++ [true] ++ bits (g n)` (two expansions and
> a copy), the ruler `1^{g n}` and the clock's counter `bits (g n)`. The guess overwrites the block
> with a stream, a separator and a budget word. The run is a phase host: a one-cell take reads the
> query's flag; in the middle it splits the block (a skip back, the lockstep walk over the ruler, a
> take of the separator, a move of the budget word), tests the budget `b ≤ g n` (its expansion and
> the length comparison with the stream), normalizes it to `bits b` (an install call), extracts `α`
> from the query's tail (the install call of the composite pair extractor), writes the core's input
> `⟨⟨bits b, α⟩, 1^{n + 1}⟩` by three emissions under the capture wrapper, and runs the interpreter
> core under the step clock over the virtual-input host, accepting at its `accept` within the
> allowance `g n`; at a top it runs the decider of `hBF` on the query's tail under the same clocked
> host and accepts iff its captured output starts with `false`. All-branch halting is
> `Turing.guessRunTM_haltsWithin` and acceptance `Turing.guessRunTM_accepts_iff`; `K` is uniform and,
> per code, `C = max 1 (max C_R C_BF)`.

## Duplication

**Both v3 screens** (`scripts/copy-text-screen-v3.py`, SHA-256 `f4feac91…`), on frozen copies of the
38-file population (`evidence/screens/population.txt`) at identical relative paths, one at a time
under `nice -n 10` (`evidence/runtime/screen.sh`):
- **base** (the base tree): "declarations screened: 2241; copy pairs (target reproduces >= half of source): 2439; reproduced text: 858,015 chars" (2,973 s); **byte-identical** to the campaign's screen base
  `eq-fill-diagonalizer-screen-base.txt` (2,241 declarations, 2,439 pairs, 858,015 characters);
- **final** (the final tree, the owned file at the last commit): "declarations screened: 2317; copy pairs (target reproduces >= half of source): 2483; reproduced text: 864,671 chars" (2,164 s);
- `evidence/screens/screen-diff.txt`: 44 new pairs, 0 gone. No base pair is gone: the
  owned file's 133 E-Q pairs are unchanged.

An earlier final screen (before the third finishing commit; its diff is kept as
`screen-diff-pre.txt`, its raw output was replaced by the re-run) found 59
new pairs, among them four at 93–94% between the hosted clock's four field lemmas (one shared
binder list) and `qy_initCfg` reproducing `dz_initCfg` at 90%, and `dz_hQ`/`dz_seg_acc` at 82% and
`dz_accepts_iff`/`dz_halts` at 88%. They were removed (one lemma `dzClkEmb_eqs`; a term-mode
`dz_initCfg`; one segment reading `dz_seg_read`; the shared bound `dz_K_bound`), and the final
screen re-run.

**Every new pair, with its disposition** (target ← source, the screen's share):

- `ClockLoop.lean::clockTM_loop` ← `NTimeDiagonalizer.lean::dzBlk_length` (73%): idiom: a `simp only [List.length_append, List.length_replicate, List.length_singleton]` length computation
- `ExhaustiveReplay.lean::xr_val_lt` ← `NTimeDiagonalizer.lean::dz_word_lt` (64%): re-derivation of another file's private (ExhaustiveReplay `xr_val_lt`, for its own `xr_val`): keep, promotion requested
- `NDHost.lean::guessRun_split` ← `NTimeDiagonalizer.lean::dz_split_stream` (98%): copy of another file's private (NDHost `guessRun_split`, the three-line list split): keep, promotion requested
- `NTimeDiagonalizer.lean::DzKit.bA` ← `NTimeDiagonalizer.lean::DzKit.bB` (75%): idiom: bank maps, `qyBank` at different offsets (as E-Q's `QyKit.bCb`, …)
- `NTimeDiagonalizer.lean::DzKit.bA` ← `NTimeDiagonalizer.lean::DzKit.bL` (82%): idiom: bank maps, `qyBank` at different offsets (as E-Q's `QyKit.bCb`, …)
- `NTimeDiagonalizer.lean::DzKit.bB` ← `NTimeDiagonalizer.lean::DzKit.bA` (83%): idiom: bank maps, `qyBank` at different offsets (as E-Q's `QyKit.bCb`, …)
- `NTimeDiagonalizer.lean::DzKit.bB` ← `NTimeDiagonalizer.lean::DzKit.bL` (81%): idiom: bank maps, `qyBank` at different offsets (as E-Q's `QyKit.bCb`, …)
- `NTimeDiagonalizer.lean::DzKit.bB` ← `NTimeDiagonalizer.lean::DzKit.bR` (53%): idiom: bank maps, `qyBank` at different offsets (as E-Q's `QyKit.bCb`, …)
- `NTimeDiagonalizer.lean::DzKit.bB_ne` ← `NTimeDiagonalizer.lean::DzKit.bR_ne` (63%): idiom: bank-tape disjointness facts
- `NTimeDiagonalizer.lean::DzKit.bL` ← `NTimeDiagonalizer.lean::DzKit.bA` (77%): idiom: bank maps, `qyBank` at different offsets (as E-Q's `QyKit.bCb`, …)
- `NTimeDiagonalizer.lean::DzKit.bL` ← `NTimeDiagonalizer.lean::DzKit.bB` (69%): idiom: bank maps, `qyBank` at different offsets (as E-Q's `QyKit.bCb`, …)
- `NTimeDiagonalizer.lean::DzKit.bR` ← `NTimeDiagonalizer.lean::DzKit.bA` (81%): idiom: bank maps, `qyBank` at different offsets (as E-Q's `QyKit.bCb`, …)
- `NTimeDiagonalizer.lean::DzKit.bR` ← `NTimeDiagonalizer.lean::DzKit.bB` (79%): idiom: bank maps, `qyBank` at different offsets (as E-Q's `QyKit.bCb`, …)
- `NTimeDiagonalizer.lean::DzKit.bR` ← `NTimeDiagonalizer.lean::DzKit.bL` (79%): idiom: bank maps, `qyBank` at different offsets (as E-Q's `QyKit.bCb`, …)
- `NTimeDiagonalizer.lean::DzKit.bR_off` ← `NTimeDiagonalizer.lean::DzKit.bR_j` (73%): idiom: bank-tape disjointness facts
- `NTimeDiagonalizer.lean::DzKit.sB` ← `NTimeDiagonalizer.lean::DzKit.sR` (68%): idiom: the two instances of `dzClkEmb` (core, decider)
- `NTimeDiagonalizer.lean::DzKit.sR` ← `NTimeDiagonalizer.lean::DzKit.sB` (69%): idiom: the two instances of `dzClkEmb` (core, decider)
- `NTimeDiagonalizer.lean::dzSetL` ← `NTimeDiagonalizer.lean::qySetT5` (57%): idiom: a layout as a `Function.update` chain
- `NTimeDiagonalizer.lean::dzSetL` ← `NTimeDiagonalizer.lean::qyTB` (63%): idiom: a layout as a `Function.update` chain
- `NTimeDiagonalizer.lean::dz_accepts_iff` ← `NTimeDiagonalizer.lean::dz_halts` (78%): idiom: the setup's facts fed to the host's halting and acceptance lemmas
- `NTimeDiagonalizer.lean::dz_clock_exists` ← `NTimeDiagonalizer.lean::qy_clock_start` (53%): idiom: the clock configuration's field reading, over `vhostSilentCfg` (the brief: state the clock's clauses afresh over `vhostSilentTM`)
- `NTimeDiagonalizer.lean::dz_qmid` ← `NTimeDiagonalizer.lean::dz_qtop` (61%): idiom: the two branches' shared flag and tail preamble
- `NTimeDiagonalizer.lean::dz_split` ← `NTimeDiagonalizer.lean::dz_tail_run` (51%): idiom: a framed row's endpoint read cell by cell
- `NTimeDiagonalizer.lean::dz_split` ← `NTimeDiagonalizer.lean::qy_wordPatch_ones` (51%): idiom: a framed row's endpoint read cell by cell
- `NTimeDiagonalizer.lean::dz_split_stream` ← `NDHost.lean::guessRun_split` (65%): copy of another file's private (NDHost `guessRun_split`, the three-line list split): keep, promotion requested
- `NTimeDiagonalizer.lean::dz_tail_run` ← `NTimeDiagonalizer.lean::qy_copy` (54%): required by the brief: `copyMapTM_run_ofCfg` directly from cell 1 (`qy_copy` assumes the word at cell 0)
- `NTimeDiagonalizer.lean::dz_tail_run` ← `NTimeDiagonalizer.lean::qy_copy_over` (59%): required by the brief: `copyMapTM_run_ofCfg` directly from cell 1 (`qy_copy` assumes the word at cell 0)
- `NTimeDiagonalizer.lean::dz_take_run` ← `NTimeDiagonalizer.lean::qy_emit_halt` (62%): required by the brief: the leaf's own step lemma (`qy_step` covers only steps that write nothing)
- `NTimeDiagonalizer.lean::dz_take_run` ← `NTimeDiagonalizer.lean::qy_step` (57%): required by the brief: the leaf's own step lemma (`qy_step` covers only steps that write nothing)
- `NTimeDiagonalizer.lean::dz_top_run` ← `NTimeDiagonalizer.lean::DzKit.bB_ne` (67%): idiom: bank-tape disjointness facts
- `NTimeDiagonalizer.lean::dz_top_run` ← `NTimeDiagonalizer.lean::dz_flag` (54%): idiom: a hosted phase and a bank fact
- `NTimeDiagonalizer.lean::dz_word_lt` ← `ExhaustiveReplay.lean::xr_val_lt` (65%): re-derivation of another file's private (ExhaustiveReplay `xr_val_lt`, for its own `xr_val`): keep, promotion requested
- `NTimeDiagonalizer.lean::dz_zero_bank` ← `NTimeDiagonalizer.lean::dz_arg_bank` (64%): idiom: the bank's heads beside the bank's tapes
- `NTimeDiagonalizer.lean::qyLocRed` ← `NTimeDiagonalizer.lean::dzSetRed` (50%): idiom: a phase host's dispatch table
- `NTimeDiagonalizer.lean::qy_main` ← `NTimeDiagonalizer.lean::dz_out_le` (54%): idiom: the `computesFunInTime_iff`/`computesInTime_iff` reading
- `NTimeDiagonalizer.lean::qy_setup_short` ← `NTimeDiagonalizer.lean::dzBlk_length` (73%): idiom: a `simp only [List.length_append, List.length_replicate, List.length_singleton]` length computation
- `Nondeterminism.lean::a3n_poly_pair` ← `NTimeDiagonalizer.lean::dz_alpha_eq` (86%): idiom: the rewrite chain `pairDecode_pairEncode`/`Option.map_some`/`getD_some`; different statements
- `Primitives.lean::incFixedTM_computes` ← `NTimeDiagonalizer.lean::dzBlk_length` (85%): idiom: a `simp only [List.length_append, List.length_replicate, List.length_singleton]` length computation
- `SeamLayout.lean::sl_read_table` ← `NTimeDiagonalizer.lean::dzBlk_length` (73%): idiom: a `simp only [List.length_append, List.length_replicate, List.length_singleton]` length computation
- `SeamLayout.lean::sl_reverse_read` ← `NTimeDiagonalizer.lean::dzBlk_length` (73%): idiom: a `simp only [List.length_append, List.length_replicate, List.length_singleton]` length computation
- `SeamLayout.lean::sl_sm_word` ← `NTimeDiagonalizer.lean::dzBlk_length` (73%): idiom: a `simp only [List.length_append, List.length_replicate, List.length_singleton]` length computation
- `Catalog.lean::clearTM` ← `NTimeDiagonalizer.lean::dzTakeTM` (61%): idiom: a one-tape row's transition-table shape; `dzTakeTM` is the ruled own leaf (no row writes a blank at one cell)
- `Catalog.lean::f2_incFixed_computes` ← `NTimeDiagonalizer.lean::dzBlk_length` (85%): idiom: a `simp only [List.length_append, List.length_replicate, List.length_singleton]` length computation
- `Catalog.lean::incrementTM` ← `NTimeDiagonalizer.lean::dzTakeTM` (59%): idiom: a one-tape row's transition-table shape; `dzTakeTM` is the ruled own leaf (no row writes a blank at one cell)

**New copies (pairs at 90% or more): one**, `NDHost.lean::guessRun_split` reproducing
`dz_split_stream` (98%): the same three-line list split (`List.drop_eq_getElem_cons`,
`List.take_append_drop`). `guessRun_split` is private to `Build/NDHost` and cannot be cited, and
`exact?` finds no public lemma; disposition (the brief's): **keep mine and request a promotion** of
`guessRun_split` (or of a public `List` lemma `s = s.take G ++ [s[G]] ++ s.drop (G + 1)`).
Likewise, below 90%, `dz_word_lt` restates ExhaustiveReplay's private `xr_val_lt` for its own
`xr_val` (65%): keep, promotion requested.

**Semantic search per private**: `evidence/dedup/semantic-search.md` (106 rows: by name in the tree
and in all 182 PR heads — no hit; by statement — the `exact?` probe found one re-derivation,
`dz_pairEncode_length` = `Turing.length_pairEncode`, removed and the published lemma cited).

## Checkpoints (one commit and one zip each, delivered at once)

| # | Content | Commit | Zip SHA-256 |
|---|---|---|---|
| 1 | overlay; `P` as a contract with its uniform bound (and, early: the take leaf, the silent-capture normal form, the generic hosted clock, the kit, the layout) | `4c15175f` | `4349d708…dcf00f6` |
| 2 | `dzTakeTM`, the flag, the tail's copy, `Q`'s phases and dispatch, the handoff | `f6b2261f` | `e69802a1…6374bcca` (full: `e69802a1d0f9995b083f4f98ee99f46ce6536374bcca7206f63f96c0c493057d`) |
| 3 | the split, the budget's test and normalization | `2a3e5f71` | `3a358a7c…428b642a` |
| 4 | `α` and the rewrite (three emissions under `embedSilentTM`, the capture rewound) | `fdc83fee` | `cfd8d2ea…bfa1eff1` |
| 5 | the clocked, hosted run's two uses and their verdict readers | `54552c0c` | `a84dca46…62a6683c` |
| 6 | `Q`'s three cases, `D`, `K` (`guessRunTM_haltsWithin`) | `a2cdad1f` | `542815ff…a6579d25` |
| 7 | the middle (both directions) and the top (`guessRunTM_accepts_iff`) | `046a6be7` | `87359dc0…4fd4152c` |
| 8 | **the target** | `c1f9a9f6` | `d9c1aac3…fd63ad29` |
| — | finishing: a proof sketch in `dz_setup_facts` (lint); `length_pairEncode` cited instead of a re-derivation (`exact?` probe); the screen's in-file near-copies removed (`dzClkEmb_eqs`, a term-mode `dz_initCfg`, `dz_K_bound`, `dz_seg_read`) | `d58aef6f`, `c1a7632c`, `7b1b9353` | final zip |

Full zip hashes are in `evidence/logs/checkpoint-zips.sha256`.

## Final checks

- **The owned file**: 0 errors, 0 warnings, no sorry warning (`evidence/logs/owned-file-check-final.log`).
- **Final sweep** of the whole order list (`evidence/logs/final-sweep.log`, each module's time and
  maximum memory): 84/84 pass, 887 s, peak 2,948 MiB (the owned file 94.0 s, 2,948 MiB). Sorry
  warnings: 18 declarations in 8 modules = the base set minus the target. The two later finishing
  commits touch only the owned file, so after the last proof edit the order list's tail from the
  owned module on was re-run (`final-sweep-tail.log`): `NTimeDiagonalizer` 63.5 s, 2,913 MiB;
  `NTimeHierarchy` 9.7 s, 2,085 MiB; `Diagonalization` 1.6 s, 1,883 MiB; all exit 0, no warning.
  `NTimeHierarchy` (which cites only the target's statement) elaborates unchanged.
- **Axioms** (`axioms-final.log`): `Turing.NTimeDiag.exists_diagonalizer` →
  `[propext, Classical.choice, Quot.sound]`. **Every new private** (the walk covers 553
  declarations: the 106 new ones and their auxiliaries — projections, matchers, equation lemmas):
  `collectAxioms` within `[propext, Classical.choice, Quot.sound]` for all (`audit-walk.out`:
  no `AXIOMS-BAD` line).
- **Lint**: `campaign_style_lint.py TCSlib/Complexity/Diagonalization`: 0 FAIL, 3 WARN over 5 files
  (as at the base: `EXPCOM`'s check 8, and the sizes of `NTimeDiagonalizer` and `NTimeHierarchy`);
  `style_lint.py` on the owned file: the size finding only (expected). No new line over 100
  characters; every new declaration has a docstring; every proof over 20 lines has a literal
  `**Proof sketch.**`.
- **Size**: 8,505 lines (base 5,432; overlay 5,435); 22 public / 320 private declarations (base 22 /
  214: 106 new privates, no new public).

## Rule 10 — the pinned base and no unfolding

- **Citations outside the file**: the audit walk (`evidence/probes/DzAudit.lean`,
  `evidence/logs/audit-walk.out`) lists the 212 other-file TCSlib constants the new declarations'
  types and values mention: 97 theorems, 88 definitions (mentioned, e.g. `guessRunTM`, `qyC`'s
  `Cfg`, `MultiTapeTM.runFrom`; never unfolded, see the seal), 12 inductives, 15 constructors. **No
  other file's private** is reached.
- **The import probe**, extended by every name cited beyond it
  (`evidence/probes/EDImportProbe-extended.lean`, generated by `mkimportprobe.py` from the walk;
  165 names added to the brief's probe), re-run: 0 errors, every name resolves, none depends on
  `sorryAx` (`evidence/logs/import-probe-extended.out`).
- **Seal test** (`evidence/seal/`): maximal, built by `mkseal_dz.py` from the generator
  `DzSealList.lean` (`seal-list.out`): `attribute [local irreducible]` on **350** definitions — every
  TCSlib definition outside the module that is semireducible, not an instance, not a projection,
  not private and not a matcher (345), plus the route probe's five same-file definitions (`query`,
  `budget`, `ladder`, `stage`, `stageCode`) — and `attribute [-simp]` on the four `@[simp]` TCSlib
  definitions (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`, `NDTM.initCfg`), placed right
  before the first new declaration (sealed lines 5704–8859). It contains the brief's whole rule-10
  list (the route probe's 11 and the 32 further names: all 43 checked). Results
  (`seal-sealed.out`, `seal-unsealed.out`, `seal-summary.txt`; 67.3 s and 64.6 s):
  - **sealed: the new code elaborates with 0 errors and 0 warnings**;
  - controls (each logs one line): 350 `rfl` delta goals, 350 first-equation goals, 4 `simp`
    unfolding goals; **all 704 fail sealed**;
  - unsealed: 691 pass; the 13 that fail are the delta goals of the 12 structurally recursive
    definitions (`sweepFold`, `runWith`, `codeReadUnary`, `codeReadVec`, `codeSkipRepeat`,
    `decFixed`, `incFixed`, `mealyRun`, `pairDecode`, `unaryTokenSplit`, `workReadsK`, `ladder`),
    whose equation controls close, and `StepBlock.summaryEmit`'s equation control, whose delta
    control closes;
  - so **every one of the 350 sealed definitions has a control that fails sealed and closes
    unsealed**, and the four erased `simp` definitions' controls fail sealed and close unsealed.
- **Inspection table** (`evidence/seal/inspection-table.txt`, `evidence/probes/inspect.py`): 1,821
  identifier rows in the new code's `rw`/`simp`/`dsimp only`/`unfold` lists and `show` steps. **No
  other-file TCSlib definition is named in a `rw`/`simp`/`dsimp`/`unfold` list** (the other-file
  names there are theorems: 101 in `rw`, 1 in `simp`); `unfold` and `dsimp only` name only the file's
  own definitions (`dzLay`, `dzQB`, `dzSetB`, `dzK`, `DzKit.K`, `DzKit.bR`, `DzKit.bB`, `dzAlpha`,
  `qyC`, `qyBody`). Five `show` steps name `FinTM.bufferTape` in the goal they state, to unfold
  only the file's own `qyC`/`dzLay`; the sealed build proves no
  other-file definition is unfolded. The leaf's step never unfolds `step` or `Action.apply`
  (`MultiTapeTM.step_of_some`, `Action.apply_*`); core/Mathlib reductions occur only in `rfl`,
  `decide`, `show` (e.g. `Fin.castAddEmb`, `Function.update`, `List.replicate`).

## Rule 11 — MIG-1 compatibility

- No R3 canonical row (`copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`,
  `incrementTM_run_succ`, `incrementTM_run_overflow`): none in the walk, none in the diff's added
  text; the framed `_ofCfg` rows are used (`copyMapTM_run_ofCfg`, `transferMapTM_run_ofCfg`,
  `walkTM_run_ofCfg`, `skipBackTM_run_ofCfg`, and through E-Q's wrappers `rewindTM_run_ofCfg`,
  `writeConstTM_run_ofCfg`, `expandTM_run_ofCfg`).
- No private declaration of another file is cited (the walk reaches none).
- All 106 new privates are under `dz`/`Dz`; no `dz`/`Dz` identifier occurs elsewhere in the tree or
  in any of the 182 PR heads (`evidence/dedup/`).
- No `deriving`: the phase indices' `DecidableEq`/`Fintype` instances are `private`, so no public
  instance name is created.

## Environment notes and deviations

- `/usr/bin/time` is absent; the timing wrapper logs the same figures (wall time, maximum RSS).
- The GitHub REST/GraphQL API is not available to this session; open PRs could not be told from
  closed ones, so the name search covered all 182 `refs/pull/*/head` (a superset).
- One Lean process at a time throughout; the screens ran `nice -n 10` beside at most one Lean
  process, one screen at a time.
- The session's worker process restarted once during the finishing sequence (after the first
  final screen). Nothing was lost: the clone, the oleans, the logs and the drafts survived, and the
  drafts were checked to reassemble byte-for-byte to the committed file before work resumed.
- The first final screen's raw output was replaced by the re-run after the third finishing commit
  (its diff is kept, `screen-diff-pre.txt`).
- No other deviation.
