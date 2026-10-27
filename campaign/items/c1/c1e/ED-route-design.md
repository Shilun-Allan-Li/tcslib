# E-D: the diagonalizer's route, before its brief (design note, maintainer, 2026-10-27)

**What this is for.** E-D is C1-E's second fill, `Turing.NTimeDiag.exists_diagonalizer`
(`Diagonalization/NTimeDiagonalizer.lean:335`), after E-Q in the same file (gate 39's
resolutions). Megafill D's triage (T2) found its hosts published but `timeConstructible_iff`
missing; A1 (#164) has since landed it, so nothing blocks E-D except E-Q's landing. This note
fixes the route against the published rows, the way `EQ-route-design.md` did for E-Q, so the
brief can be drafted while E-Q's fill runs. Its decisions are at the end.

The docstring's sketch is the starting point: `D` is a nondeterministic phase host over the
query, a guessed stream with a nominal budget, the middle (the interpreter core under the step
clock) and the top (`hBF`'s decider under the virtual-input host and the clock).

## What is published (the pieces, at #169's merged head `9d0af8cb`)

- **The guess-then-run host** `Turing.guessRunTM` (`Build/NDHost`), which is
  `Turing.NDTM.phaseHostND` over six phases: a deterministic setup `P` (to its exit `pexit`),
  the choice writer over a nonblank block of `m` cells on a tape `j`, a step right, the
  rewind, a deterministic run `Q` from `guessRunCfg` (the block overwritten by the stream) up to
  a live verdict `acc` or `rej`, and the verdict bit. Proved:
  - `guessRunTM_haltsWithin`: if every stream's run reaches a verdict within `T`, every branch
    halts within `TP + 2m + T + 11`;
  - `guessRunTM_accepts_iff`: at every budget `B ≥ TP + 2m + T + 11`, some choice word of
    length exactly `B` halts with output `[true]` (that is `FinNDTM.AcceptsWithin`'s shape) iff
    some stream makes the run's first verdict `acc` **with an empty output** at that time;
  - `guessRunTM_silent_spec`: the same for a **clean** setup with the core embedded silently.
    `Diagonalization/NTimeHierarchy`'s `exists_timed_universal_NDTM` uses it.
- **The query:** E-Q's statement `exists_queryTM` (a deterministic `G` computing `query f g`
  within `C · (g n + 1)`), called on the native input by `FinTM.exists_inputCallTM` (exit at
  `Cfg.ofWords exit (stateWord C.k (query f g x))`, its entry and exit possibly equal: run it
  released, as E-Q's review F1 found).
- **`g`'s witness** through A1's `Complexity.timeConstructible_iff` (`n ≤ g n`, and a machine
  computing `bits (g |x|)` within `c · (g |x| + 1)`), called the same way; the block by
  `Turing.expandTM_run_ofCfg` from `bits (g n)`.
- **The interpreter core** `Turing.exists_ndInterpreterCore` (`NDCodeSimulator`, now through the
  startup, #169): from `⟨some entry, 1, s on tape j, …⟩` on `⟨⟨bits t, α⟩, x⟩` with `t ≤ |s|`, a
  first verdict at `T ≤ C_R · (t + 1)`, `accept` iff the coded machine's branch along `s.take t`
  halts with `[true]`. The prefix clause (with its `|x|` term) is not used.
- **The step clock** `Turing.exists_stepClockTMVia` (`Build/StepClock`): body steps counted
  against a binary counter `w` (value `d`); `finish` with the body at its first stop `τ ≤ d`
  within `5τ + 2|w| + 2`, or `timeout` at `d` within `5d + 2|w| + 2`; a frame clause.
- **The virtual-input host** `Turing.vhostSilentTM` (`vhostSilentTM_runFrom`): a machine run on
  a buffer tape's word as its input, its emissions captured. Both simulators read their inputs
  natively, and here their inputs are work-tape words, so both run hosted.
- **Rows for the setup and the rewrite:** the pair extractors (`prefixCanonTM` with
  `FinTM.pairExtractTM`: on `pairEncode a x` it emits `F a`, so the second-component extractor
  on the query's tail emits `α`), the copy and clear rows, `writeAdvTM`, the rewinds, the phase
  host `phaseHostTM` with its published equations, and the seams. **No machine-level
  `pairEncode` writer is published** (`copyMapTM` maps cell to cell; `PolyTimeComputable.pairEncode`
  is polynomial, at the class level). E-Q's brief licenses one as its leaf L6 (each bit written
  1, 2 or 4 times: exactly the shape `⟨⟨bits b, α⟩, x⟩` needs).

## The shape (recommended)

`D := guessRunTM P pexit j Q qentry acc rej`, bundled as a `FinNDTM`. One guessed block holds
the stream and the nominal budget: `m = g n + L` with `L = |bits (g n)|`. Its first `g n` bits are
the stream `s` and its last `L` bits the budget word `w_b`.

- **`P` (deterministic, the setup):** the query call on `1ⁿ` (released); `g`'s witness, giving
  `bits (g n)` (released); the block, `expandTM` of `bits (g n)` (`g n` cells) followed by a copy
  of `bits (g n)` (`L` more nonblank cells), with blanks on both sides; the counter `bits (g n)`
  for the clock on its own tape; rewinds. It first reaches `pexit` at
  `TP ≤ P₀ · (g n + 1)`, uniform (no code-dependent term: the query is `O(g n + 1)` by E-Q, and
  `|query| = O(g n + 1)`).
- **`Q` (deterministic, the run):** a phase host over:
  1. **the flag:** read the query word's first cell: `[]` (not unary, or `n < 3`) goes to `rej`;
     `true` to the top; `false` to the middle;
  2. **the middle's preparation:** copy `w_b` off the block and clear its `L` cells, so that the
     block tape holds exactly `bufferTape s`, the core's stream tape (`t = b ≤ g n = |s|`);
     reject unless `b ≤ g n`; normalize to `bits b`; extract `α` by one hosted call of the
     second-component extractor on the query's tail; and write the core's input
     `⟨⟨bits b, α⟩, 1^{n+1}⟩` on a buffer (`1^{n+1}` from the input's length), by E-Q's writer;
  3. **the middle's run:** the clock (counter `bits (g n)`, allowance `g n`) over
     `vhostSilentTM R`, stopping at `R`'s `accept` and `reject`. `finish accept` goes to `acc`;
     `finish reject` and `timeout` go to `rej`;
  4. **the top's run:** the clock over `vhostSilentTM BF` on the query word's tail
     `⟨⟨bits T*, α⟩, 1^a⟩`, stopping at `BF`'s halt; then read the captured bit: `[false]` goes
     to `acc`, anything else to `rej`. A `timeout` goes to `rej`.

  Every run is silent (both simulators are hosted silently), so the run's output is empty at
  its verdict, as `guessRunTM_accepts_iff` requires.

**Time, uniform.** `TP + 2m + T + 11` with `m ≤ g n + L ≤ 2 (g n + 1)`, and `T` the preparation
`O(g n + 1)` plus the clock's `5 g n + 2L + 2` plus the dispatches. So `K = P₀ + Q₀ + 7 + 15`, a
uniform constant, and `guessRunTM_haltsWithin` gives `D.tm.HaltsWithin x (K · (g |x| + 1))`.
Off unary inputs the query is `[]` and `Q` rejects at once; the bound holds the same way.

**The middle, per code `α`** (`C = max 1 (max C_R C_BF)`):
- **Completeness:** the coded machine accepts `1^{n+1}` along a word `v` with `|v| = t'` and
  `C · (t' + 1) ≤ g n`. Take the stream `v` padded to `g n` bits, and the budget word
  `bits t'` padded with zeros to width `L` (`t' ≤ g n`, so it fits). The test passes, the core
  runs on `⟨⟨bits t', α⟩, 1^{n+1}⟩` and accepts at `T ≤ C_R · (t' + 1) ≤ g n`, inside the
  allowance: `finish accept`. Then `guessRunTM_accepts_iff` gives the accepting branch at the
  budget `K · (g n + 1)`.
- **Soundness:** an accepting branch has a stream `s` and a budget `b ≤ g n` whose core run
  accepts inside the allowance, so the coded machine's branch along `s.take b` halts with
  `[true]` (the core's clause): `AcceptsWithin (1^{n+1}) b`, and `AcceptsWithin.mono` to `g n`.

**The top:** `BF` on `⟨⟨bits T*, α⟩, 1^a⟩` completes within `C_BF · 2^{C_BF · (T* + 1)} ≤ n ≤ g n`,
inside the allowance. So `D` accepts iff `BF` answers `[false]` iff the coded machine does not
accept `1^a` within `T*`. Every stream gives the same verdict, so one stream suffices.

## Leaves and sizes (ESTIMATE)

| Piece | Lines | Notes |
|---|---|---|
| `P`: the two released calls, the block, the counter, rewinds | 300–500 | the pattern of UN's setup (`NTimeHierarchy`), which is a seam chain of eight phases; cite its rows, not its proof |
| The flag reader and the two verdict readers | 100–200 | one-step leaves (a read and a redirect) |
| The budget's test and normalization | 200–400 | **leaves**, unless E-Q's fill publishes a binary `≤` row in the same file (its L2): then cite it (same-file privates are citable) |
| The rewrite: extract `α`, write `⟨⟨bits b, α⟩, 1^{n+1}⟩` | 200–500 | one hosted extractor call; E-Q's writer L6 (the same shape, the review's `rv_query_word`), cited in the file; without it, a doubling writer is a further leaf of 200–400 |
| The two clocked, hosted simulators | 300–500 | `exists_stepClockTMVia` over `vhostSilentTM`; the frame clause for the untouched tapes |
| `Q`'s phase host, `D`'s bundling, the transfer and the contract | 300–600 | `guessRunTM_haltsWithin`, `guessRunTM_accepts_iff` |
| **Total** | **1.5k–2.8k** | C1-E's estimate was 1–2k, before the nominal budget and the hosting |

## Copy hazards the brief names

- `NTimeHierarchy`'s `exists_timed_universal_NDTM` and `un_setup`: the same guess-then-run pattern
  with a clean setup; E-D's setup is not clean (it keeps the query word and the counter), so it
  uses `guessRunTM_accepts_iff` directly, not `guessRunTM_silent_spec`. Cite the host's lemmas,
  never re-walk the writer or the handoff.
- E-Q's privates in the same file (the locator's arithmetic, the writer): cite them by name
  where they fit; a second binary `≤` or a second `pairEncode` writer in the file is a copy.
- `ExhaustiveReplay`'s capped replays (`xr_replay_finish`/`_timeout`): cite the clock's clauses.
- B5a's hosted-verdict junction and the core's junction: the same embedding-and-field identities;
  copy nothing, use `embedEmitCfg_eq` and the field equations.
- `SeamLayout`'s `sl_rewrap` and `Cfg.mapState_mapState` idioms (accepted idiom pairs).

## Decisions

1. **Timing.** (a) **After E-Q lands** (recommended): E-D can then cite E-Q's private leaves in
   the same file (the binary `≤`, and the writer, which no published row replaces), and the
   brief's line numbers are final.
   (b) In parallel with E-Q, on disjoint regions of the file: E-D starts sooner, but it would
   re-derive E-Q's leaves (a same-file copy for the dedup window), and the second landing
   rebases onto the first.
2. **The guess.** (a) **One block for the stream and the budget word**, through `guessRunTM`
   (recommended: its halting and exact-acceptance lemmas are published, and it is the
   docstring's `phaseHostND`). (b) Two guesses through `phaseHostND` directly: a second writer
   phase, with the handoff and acceptance re-proved, which re-derives `guessRunTM`'s lemmas.
3. **The nominal budget's form.** (a) **A binary word of width `|bits (g n)|`, tested
   (`≤ g n`) and normalized** (recommended: the docstring's sketch; two small leaves, or E-Q's
   row). (b) A unary marker in a second `g n`-cell block, converted to `bits b` by an amortized
   counter (no test, no normalization; the block doubles, and the conversion loop is a new leaf
   of its own).
4. **The queue** (with E-Q's outcome): E-D alone in a later megafill (Codex), or paired with
   another ready item. This waits for E-Q's delivery.
