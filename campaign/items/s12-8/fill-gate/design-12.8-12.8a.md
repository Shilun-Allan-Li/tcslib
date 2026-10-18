### 12.8 Configuration-graph rows (design draft, 2026-10-10; for the statement phase)

*Drafted from the S1 research (maintainer-commissioned), recorded for the user's decisions 12.8.1–12.8.6. The maintainer's alternative for 12.8.1 is at the end.*

**Why.** The user chose design A for S1b, the summit of `ConfigGraph.lean`:
a configuration-level simulator built on §12 rows (decision log, 2026-10-10).
The S1 research found six capabilities that no public row provides.

| Gap | Missing capability |
|---|---|
| GAP-1 | a native-input-dependent clean seam |
| GAP-3 | a framed compare |
| GAP-4 | a configuration codec with transition application |
| GAP-5 | writing a word at a displaced head |
| GAP-6 | seek over delimited records |
| GAP-7 | two continuations after `counterLoopTM` |

This note proposes reusable rows for all six. Their consumers are every
configuration-graph walker of the campaign:

- S1b (`NSPACE ⊆ DTIME(2^{O(S)})`, hence `NL ⊆ P`);
- Savitch;
- the `PATH` reduction;
- the space hierarchy;
- `TQBF ∈ PSPACE`;
- `NP ⊆ PSPACE`.

**Constraints.**

- (i) **G1** is generalizing `Build/Embed`, `Build/Seam`, Catalog's R3
  sweeps and `FinTM.bufferTape` to `{Symbol : Type*}` in place. A row that
  extends those files' private traces waits for the G1 gate.
- (ii) **G2** (`copyMapTM`/`transferMapTM`) owns the mapped-sweep scanner in
  Catalog. Rows of that family are coordinated with it: one trace per routine
  family.
- (iii) Every row has a framed contract in the §12.6/§12.7 shape (template
  below).
- (iv) The campaign deciders are `FinTM Bool`. `incrementTM`, `decrementTM`,
  `counterLoopTM`, the compare contracts and the Loop hosts stay at `Bool` after
  G1. The record layer is therefore **binary**: decision 12.8.1.

#### Contract template (all rows)

For a tape `i` and a word `w`, write **`Delim d i w`** for the §12.6
hypothesis `∀ p, -1 ≤ p → p ≤ |w| → d.workTapes i (d.workTapePos i + p) =
bufferTape w p`. That is, `w` sits at the head with blanks at `-1` and `|w|`.
Each row `R` states, from any `d` in its start phase:

1. **Exact time** `τ`: `R.runFrom d τ = finish`, where `finish` is `d` with only
   the listed cells and control changed. Every other cell, every head, the
   native input position and the output are unchanged unless the row says
   otherwise.
2. **No earlier exit:** `∀ t < τ, state ≠ done`. (For verdict anchors, this is
   `∀ b`.)
3. **Trajectory:** touched heads stay in a stated interval, typically
   `[pos − 1, pos + |w|]`, and the other heads are fixed. Space follows by
   `MultiTapeTM.spaceUsedByTape_le_card_Icc`. That lemma lives in
   `Build/Zone.lean`, so Catalog rows cannot cite it; 12.2c item 9's Zone split
   is its natural moment to move down.

The time constants below are indicative. The statement phase fixes them by
the executed pre-ship check, as in §12.6 practice.

Where an exact closed form is unnatural (R8.7's step row), the contract is the
first-return form instead: `∃ t ≤ B`, plus the no-earlier-exit clause.
`counterLoopTM` consumes it with `τ :=` that `t`, which is unique (decision
12.7.3).

#### R8.1 Framed compare (GAP-3)

- `compareTM_run_ofCfg (fst snd) (hne : fst ≠ snd) (u v) (d)
  (hstate : d.state = some .run) (hu : Delim d fst u) (hv : Delim d snd v)`.
  - Exact time `2·δ + 2`, with `δ` the first index where `u` and `v` differ or
    either word ends (`δ ≤ min |u| |v|`, the private `catalog_compare_stop`).
  - Finish: `d` with state `done (decide (u = v))`, every tape unchanged.
  - No earlier `done b`. Trajectory: both heads in `[pos−1, pos+δ]`.
- **Alphabet:** generic with `[DecidableEq Symbol]`. G1 makes `compareTM`'s
  definition generic and keeps its contracts at `Bool`, so the framed row is
  stated generically from the start, and the canonical `compareTM_run` is
  re-derived from it by a sanctioned body swap, exactly as §12.6 did for
  copy/transfer/clear.
- **Trace:** generalize `catalog_compare_trace`, `catalogCompareF` and
  `catalogCompareR` over an outer frame and two start coordinates, on the
  shared `catalog_trace_run` skeleton. No second trace.
- **Home:** `Build/Catalog.lean`, **after the G1 gate**.
- **Note:** a record is a list of blank-separated fields (R8.7), so
  `recordEqTM` is `F` framed compares with R8.3 seeks between them.

#### R8.2 Fold: a finite-state scan with a verdict (new family member)

- `foldTM (i) (δ : A → Symbol → A) (a₀ : A) [Fintype A] [DecidableEq A]`.
  Phases are the forward pass `scan a`, the return `rewind a`, and the anchor
  `done a`.
- `foldTM_run_ofCfg (hw : Delim d i w)`:
  - exact time `2|w| + 2`;
  - finish: `d` with state `done (w.foldl δ a₀)`, all tapes unchanged;
  - no earlier `done`; trajectory `[pos−1, pos+|w|]`.
- **Why a row:** every read of a record field into finite control is a fold.
  That covers the state field, the tag field, "find the marked cell and its
  content and whether it sits at a field end", record validity, and
  acceptance tests. Validators elsewhere (TQBF's well-formedness pass, the
  `PATH` shape checks) are folds too.
- **Alphabet:** generic. **Trace:** `catalog_trace_run` with a read-only
  forward family, as for `copyTM` without the destination. **Home:** Catalog,
  after G1.

#### R8.3 Seek over delimited words and records (GAP-6)

- `skipTM i`: from `Delim d i w`, move right to the word's right delimiter
  and one cell beyond, the next word's first cell. Exact time `|w| + 1`; no
  write; trajectory `[pos, pos+|w|+1]`. `skipBackTM i` is the mirror, starting
  on the cell after the left delimiter of the previous word.
- `skipTM_run_ofCfg` and `skipBackTM_run_ofCfg` have the template shape, with
  the finish `{d with workTapePos i := pos + |w| + 1}`.
- `seekFieldsTM i m` (`m` fixed) composes `m` skips by `seamCompTM_run_ofCfg`.
  `seekEndTM i` skips until the next word is empty (two consecutive blanks);
  it is a fold-guarded loop, under the same skeleton.
- **Consumers:** record navigation (R8.7, S1b's table, Savitch's frame stack),
  and **G4**, which "scans outward across zones, using the separators". Both
  skip blank-separated words, so G4 should cite `skipTM` rather than trace its
  own scan.
- **Trace:** this is the forward half of the R3 trace. Add a forward-only
  sibling of `catalog_trace_run` (`catalog_forward_run`, private), to be shared
  with R8.2's forward phase.
- **Alphabet:** generic. **Home:** Catalog, after G1, **coordinated with G2/G4**.

#### R8.4 Writing words at displaced heads (GAP-5)

- **Computed words** are G2's `copyMapTM`/`transferMapTM` (`merge` and
  `extract`). With `extract := fun _ => b` they fill a blank-free interval with
  a constant (`fillTM i b` is the in-place case `src = dst`, which G2 must
  admit or state separately). Nothing new: G2.
- **Fixed words**: `writeConstTM i (w₀ : List Symbol)` writes the hardwired
  `w₀` from the head and returns.
  - `writeConstTM_run_ofCfg`: exact time `2|w₀| + 1`; finish: cells
    `[pos, pos+|w₀|)` hold `w₀` (old contents arbitrary), head back at `pos`;
    trajectory `[pos, pos+|w₀|]`.
  - The machine is a straight-line chain; its proof uses the public
    `FinTM.emit_run` pattern adapted to writes, so it shares no Catalog trace.
  - **Home:** new `Build/Scan.lean`; **can land now**.
  - **Consumers:** record field initializers (state code, tag code), marker
    cells, per-round patterns inside R8.6's body.

#### R8.5 Native-input rows (GAP-1)

All three are generic over `Symbol`, cite the public `FinTM.rewind_scan` and
`timed_rewind`, and live in new `Build/Scan.lean` (**now**). EmitIterBody's
private startup (`body_start`, `copy_step`, `rwTape_*`, `rwInput_*`) is the
same routine and should be re-derived from `inputCopyTM` in 12.2c T2 (CH7-D2,
coordinated with Aparna).

- `inputCopyTM i`: copy the native input onto tape `i` from the head, then
  rewind both heads.
  - Start: input head at `1`, `Delim`-free destination (old contents
    arbitrary).
  - Exact time `2|x| + c`. Finish: `[pos, pos+|x|)` holds `x`, input head at
    `1`, tape head at `pos`.
  - Trajectory: input head in `[0, |x|+1]`, tape head in `[pos−1, pos+|x|]`.
- `inputLengthTM i`: count `|x|` into a fixed-width binary counter on tape `i`
  (one `incrementTM` per input symbol, cited at its framed carry-sensitive cost).
  - Exact time `Σ_v (2·ν₂(v) + 2) + |x| + c`, amortized at most `4|x| + c`
    (§12.7's potential).
  - Finish: the counter holds `bits |x|` padded to its width, and the input head
    is back at `1`.
  - Bool only, because it uses `incrementTM`. Its home is `Build/CounterLoop.lean`
    or `Scan` importing it.
- `inputSeekTM i c`: move the input head to the binary position `p` held at
  tape `i`.
  - Mechanism: copy `p` to the counter tape `c` (`copyTM_run_ofCfg`), rewind the
    input (`timed_rewind`), then `counterLoopTM` with the one-step body "input
    right".
  - Exact time: the copy (`2|p| + 2`), the rewind (`≤ pos + 2`), then
    `p + counterOverhead w (p + 1)`.
  - Finish: input position `p`, counter tape all-`true` (`counterLoopTM_run_done`).
    Callers clear it (`clearTM_run_ofCfg`).
  - Bool only.
  - **Consumers:** R8.7's input read, `PATH_mem_NL`'s matrix indexing (`u·n + v`),
    virtual-input callers needing random access.
- Packaged combinator **`exists_inputCallTM`** = `inputCopyTM` +
  `exists_installCallTM`: call a function-level machine on the native input at a
  clean seam. It is GAP-1's general form. **Home:** new `Build/InputCall.lean`,
  importing Loop, **now**. It touches no G1 file, but must not collide with
  12.2c T1 item 11's Loop edits.

#### R8.6 Counter-driven expansion

- `expandTM (pat : List Bool)` = `counterLoopTM` around `writeConstTM pat`
  followed by a `skipTM`-like advance. From a counter word of value `d` at the
  counter tape and a blank region on tape `i`, it writes `pat` `d` times
  contiguously.
  - Exact time `Σ_{r<d} τ_pat + counterOverhead w (d+1)`, by
    `counterLoopTM_run_done` and `counterLoop_time_le`.
  - The written word is `pat`ⁿ with `n = d`, which is a framed `Delim` for later
    rows.
- **Consumers:**
  - S1b and Savitch: blank tape fields of `2s+1` cell codes, with `s` given in
    binary by the constructor;
  - `spaceConstructible_logSpace`/`_linear`/`_poly` (binary ↔ unary);
  - the space hierarchy's budget loop;
  - the §12.7 clocks.
- Bool. **Home:** `Build/CounterLoop.lean` (not G1-owned). **Can land now**,
  once R8.4's `writeConstTM` exists.

#### R8.7 Configuration records (GAP-4)

**Pure layer** (new `Build/CfgRecord.lean`; statements now).

- **Parameters:** a source `M : MultiTapeTM k Bool Q`, `[Fintype Q]`, a window
  radius `s`, an input length `n`, and a finite **tag** type `T` with an update
  `upd : T → Option Bool → T`. The tag carries emission history; the
  configuration graph instantiates `T := OutSummary` and `upd` := the Q1 append
  table. A Build-level row cannot mention `OutSummary`, which is defined
  downstream in `ConfigGraph.lean`; hence the parameter.
- **`cfgRecord n s (c : Cfg k Bool Q x) (τ : T) : List (List Bool)`**, a list of
  `k + 3` **blank-separated fields**, each a blank-free Bool word:
  - **F0** state: a one-hot code of `c.state : Option Q`, width `|Q|+1`;
  - **F1** input position: `c.inputPos` in little-endian binary at the fixed
    width `|bits (n+1)|`;
  - **F2…F(k+1)** tape `i`: `2s+1` three-bit cells
    `(nonblank, value, head-here)` for `z = −s … s`;
  - **F(k+2)** tag: a one-hot code of `τ`.

  Field lengths depend only on `(n, s)`, so records compare field-wise and
  enumerate by counting.
- **`recordTape`** lays the fields out with one blank between fields (and
  between records); the G3 carrier's separator discipline.
- **Window predicate.** `Turing.Cfg.InWindow s` already exists, defined in
  `ClassPSPACE/TQBF.lean`, *downstream* of every Build file. **Decision
  12.8.2:** relocate it verbatim (same name and body) to `CfgRecord.lean` and
  delete TQBF's copy. That is a surface move in a C1d-owned file, so it waits
  for C1d. The alternative is a second predicate under another name, a
  definitional duplicate.
- **`cfgRecord_inj`:** for `InWindow s c` and `InWindow s d` on the same input,
  `cfgRecord n s c τ = cfgRecord n s d τ' ↔ core c = core d ∧ τ = τ'`. It
  follows `ConfigCount.coreCode_inj`.
- **`cfgRecord_valid`:** a word list is a record iff a fold (R8.2) accepts each
  field. One-hot fields, three-bit cells with exactly one head mark per tape
  field, and `F1 ≤ n+1` (the last by `compareTM` against `bits (n+1)` or by
  a fold).

**Rows** (`Build/CfgRecord.lean`). The statements can be drafted now. The
fills need R8.1–R8.3, so they come after the G1 gate.

| Row | Effect (framed; record at the head of tape `r`; scratch tapes blank) | Built from |
|---|---|---|
| `recordReadTM` | Verdict `done (q, ι, σ, τ, edge)`: state, the input symbol at the coded position, the `k` scanned symbols, the tag, and which tape heads sit at a field end. Record unchanged; input head restored | R8.2 folds per field, R8.3 seeks, R8.5 `inputSeekTM` on a copy of F1, `clearTM` |
| `recordApplyTM a` (`a : Action k Bool Q` fixed, `upd` fixed) | Rewrites the record of `c` into that of `a.apply c`, with the tag updated by `a.output`. Per tape it rewrites the marked cell and moves the mark; F1 gets `incrementTM`/`decrementTM` (framed), with the clamp read off the edge data; F0 and the tag go through `writeConstTM`. Precondition: no mark leaves its field (checked by the read) | R8.4, R8.3, Catalog `incrementTM_run_*_ofCfg`, CounterLoop `decrementTM_run_*_ofCfg`, and one local `markShiftTM` per tape field (new, record-specific) |
| **`recordStepTM M upd`** | **The GAP-4 row.** Verdict `done true` with the record of `M.step c` (tag updated) if that configuration is in the window. Verdict `done false` with the record unchanged otherwise, or if `c` is halted (`done true`, unchanged: a halted vertex is its own successor). First-return contract, `t ≤ C_M·(L + n + 1)` with `L` the record length; trajectory inside the record interval and `[0, n+1]` on input | `recordReadTM` ; finite dispatch on `M.tr` ; `recordApplyTM a`, glued by `seamCompTM_run_ofCfg` and two-continuation dispatch (R8.8). An NDTM is consumed per choice bit through `NDTM.fixChoice` (S1a's promotion) |
| `recordInitTM` | Writes the record of `M.initCfg x` with tag `τ₀`, from a radius word (binary `s`) and the input length counter | R8.4, R8.5 `inputLengthTM`, R8.6 `expandTM` |
| `recordEqTM` | Verdict: the two records at the heads of tapes `r`, `r'` are equal | `k + 3` R8.1 compares with R8.3 seeks |
| `recordTestTM P` (`P` a finite predicate on `(state, tag)`) | Verdict `P (c.state, τ)`. Acceptance is `P := (· = none) ∧ (· = accept)` | R8.2 on F0 and the tag field |
| `recordNextTM` | Lexicographic successor among *valid* records (odometer over all field bits, skipping invalid ones), or an overflow verdict | `incrementTM` per field, carry cascade, `recordValidTM` |
| `recordValidTM` | Verdict `cfgRecord_valid` | R8.2 |

**Space.** Every record row is framed inside its record interval plus
`O(L)` scratch. `L = O(k·s + log n + |Q|)`, which is `O(S n)` for Savitch at
`S ≥ logSpace`. This is why F1 is **binary**: a one-hot input track would make
`L = Θ(n)` and break `SPACE(S²)` at `S = log`.

#### R8.8 Two continuations after a two-exit host (GAP-7)

- Promote the existing private `Turing.seamComp_left` (`Build/Seam.lean:173`)
  as **`seamCompTM_runFrom_left`**, statement unchanged. This is SC-4's
  resolution: "expose the existing prefix lemma … do not copy its induction".
- Add one corollary, **`seamCompTM₂_run_ofCfg`**: for a host with two live
  anchors `e₁`, `e₂` (`counterLoopTM`'s `done` and `escape`), nesting two
  `seamCompTM`s attaches a continuation to each. It states the run along
  whichever exit is reached, with the other continuation's summand
  unreachable.
- Generic after G1. **Home:** `Build/Seam.lean`, **after the G1 gate**.
- **Consumers:** every `counterLoopTM` user with an early exit. S1b's BFS
  (queue empty / counter exhausted), the space hierarchy's budget loop
  (success / cap), and `recordStepTM`'s internal dispatch.

#### Placement and timing

| Row(s) | Home | Touches a G1-owned file? | When |
|---|---|---|---|
| R8.4 `writeConstTM`; R8.5 `inputCopyTM`, `inputSeekTM`, `inputLengthTM` | new `Build/Scan.lean` (imports CounterLoop) | no | **now** |
| R8.5 `exists_inputCallTM` | new `Build/InputCall.lean` (imports Loop, Scan) | no | **now** (coordinate with 12.2c item 11) |
| R8.6 `expandTM` | `Build/CounterLoop.lean` | no | **now**, after `writeConstTM` |
| R8.7 pure layer, `InWindow` relocation | new `Build/CfgRecord.lean`; `ClassPSPACE/TQBF.lean` | no; TQBF is C1d's | statements now; relocation after C1d |
| R8.1 framed compare; R8.2 fold; R8.3 seek | `Build/Catalog.lean` | **yes** | **after the G1 gate**, with G2 (shared scanner) |
| R8.4 fill (in-place mapped sweep) | Catalog (G2) | **yes** | with G2 |
| R8.8 seam promotion + corollary | `Build/Seam.lean` | **yes** | **after the G1 gate** |
| R8.7 record rows (fill) | `Build/CfgRecord.lean` | no, but cites R8.1–R8.3 | fill after R8.1–R8.3 land |

The process is the house one: maintainer-drafted statements; an executed
pre-ship check (concrete configurations, displaced heads, nonblank outer
frames, `w = []`, `s = 0`, `k = 0`, a halted source); a short statement gate;
fill batches split now/after-G1; a fill gate.

#### Consumers: which rows each walker uses

| Consumer (audited sketch) | Rows |
|---|---|
| **S1b** `NSPACE_subset_exp_dtime` (BFS; then `NL_subset_P` and Ex 4.3 by the binding route) | R8.7 `recordInitTM`, `recordStepTM` (×2 choice bits), `recordEqTM`, `recordTestTM`; R8.3 table navigation; R8.4/G2 append and counter initialization; R8.6 window fields; R8.8; existing `counterLoopTM`, `embedSilentRetTM_run` (constructor capture), `seamCompTM_run_ofCfg`, `copyTM_run_ofCfg` |
| **Savitch** `savitch` ("frame stack … catalog copy/compare/increment … one extra bank runs the vertex-adjacency test") | `recordStepTM` + `recordEqTM` for `adj(u, v)` (`u = v ∨ step u = v`, both choice bits); `recordNextTM` + `recordValidTM` for the midpoint enumerator; R8.3 seek over the frame stack; `copyTM`/`clearTM` for frame push/pop at **fixed intervals** (note 7); `incrementTM` for the depth field; R8.8 for the recursion's two returns. Space contracts of every row are load-bearing |
| `spaceConstructible_poly`/`_logSpace`/`_linear` | R8.5 `inputLengthTM`; R8.6 `expandTM`; `incrementTM` |
| **`PATH_NLComplete`** hardness (adjacency "by one local transition-table check", logspace) | The sketch's engine is the ARM layer (`arm_decides`). Optionally, a TM route: `recordStepTM`'s space clause with binary F1 gives `O(log n)`-space adjacency deciders for the index languages. Decision 12.8.4 |
| **`PATH_mem_NL`** (matrix indexing) | R8.5 `inputSeekTM` (once a nondeterministic host exists, SC-3) |
| **Space hierarchy** `space_universal`, `space_hierarchy` (interval counters, core-count clock, budget loop, probe/replay over fixed banks) | `incrementTM`/`decrementTM` (interval counters), `counterLoopTM` + R8.6 (clock and budget loop), R8.8 (success/cap exits), R8.1 (`max − min + 1 > s` against the budget word), `clearTM` resets. It simulates a *coded* machine, so not R8.7 |
| **`TQBF_mem_PSPACE`** (validate-first, depth-first assignment walker, per-clause CNF evaluation) | R8.2 folds (validation, clause evaluation), R8.5 `inputSeekTM` (re-reading prefix bits and matrix bytes), `incrementTM` / a trit odometer (`recordNextTM`'s carry discipline) for the walker, R8.3 seek on the assignment word |
| `NP_subset_PSPACE` | existing `incrementTM` (certificate enumerator) and `vhostEmitTM` (virtual input); R8.8 for accept/exhaust |

#### S1b's machine plan as a composition of these rows

**Host.** A `FinTM Bool`. It has the native input; the constructor's embedded
tapes plus a capture tape; tape `Tab` (the record table); `Cur₀` and `Cur₁`
(successor workspaces); `Rad` (radius and length words); scratch for
`recordStepTM`; and `Cnt`, the counter, which is the last tape, as
`counterLoopTM` requires.

1. **Radius.** Run `M_S` (from `hS`) under `embedSilentRetTM_run`, with its
   output `bits (S n)` captured, then rewind the input (`timed_rewind`). Its time
   is at most `M_S.configBound n (a·S n)` (`ComputesInTime.of_spaceUsed_le`).
   Multiplying by `c₀` is a fixed binary shift-and-add or `c₀` copies.
2. **Initial table.** Lay down `recordInitTM` (via `inputLengthTM` and
   `expandTM`) on `Tab`, with tag `empty` and a one-bit flag field `[false]`
   ("unprocessed") appended to each record.
3. **Counter.** Copy `Tab`'s first record's fields to `Cnt` contiguously
   (`copyTM_run_ofCfg` + `skipTM`), then fill it with `true` (G2 in-place map).
   Its value `2^{bits(record)} − 1` exceeds the record count `V`, so `done` is
   unreachable before `escape` (or is wired anyway by R8.8).
4. **Round** (the `counterLoopTM` body, anchor `a`). `seekFieldsTM` finds the first
   record whose flag is `false`; if there is none, it reaches the body's exit, and
   the host escapes. Otherwise:
   - copy that record to `Cur₀` and `Cur₁`;
   - run `recordStepTM (N.fixChoice false)` on `Cur₀` and
     `recordStepTM (N.fixChoice true)` on `Cur₁`;
   - for each successor in the window, scan `Tab` with `recordEqTM`, and if it
     is absent, append it at `seekEndTM` with flag `[false]`;
   - set the processed record's flag (`incrementTM` on the one-bit field);
   - clear the workspaces, rewind `Tab` (`skipBackTM` to the table start), and
     return to `a`.

   The round's first-return time `τ` is at most `C·(|Tab| + n + L)` with
   `|Tab| ≤ V·(L + F)`.
5. **Verdict.** From either exit (R8.8), fold `recordTestTM accept` over
   `Tab`'s records and emit `[true]` or `[false]`; then halt (a fixed emission
   tail; `FinTM.emit_run` pattern).
6. **Correctness:**
   - The table is the windowed-reachable set: the BFS invariant, with each record
     identified with a `coreSum` by `cfgRecord_inj` at `T := OutSummary`.
   - Membership follows by S1a's targets 1–4 and the audit's note-6 bridge
     (canonical decoding, outside-window rejection by `recordStepTM`'s false
     verdict, path lifting from the true initial configuration, all accepting
     vertices tested, the initial vertex in the table).
7. **Time:**
   - `counterLoop_time_le`: `V·B + 4V + 2|w| + 2` with `B = O(V·L + n)`. Add the
     constructor and startup.
   - Everything is at most `K·2^{c'(S n+1)}`, by the generalized `configBound`
     arithmetic and `n + 2 ≤ 2^{S n + 1}`.
   - All budgets are evaluated at `n` itself. **No monotonicity of `S` is used.**

#### Decisions for the user (12.8.x)

1. **Binary records** (recommended). The rows stay on the `Bool` counter stack,
   with no generic increment or `counterLoopTM`. The alternative is a
   rich-alphabet record: one cell per simulated cell, a simpler step machine, and
   `alphabet_reduction{,_spaceUsed}` at the end. It needs `incrementTM`,
   `decrementTM` and `counterLoopTM` generalized over two designated digit
   symbols (Catalog is G1-owned; CounterLoop is not).
2. **`Cfg.InWindow` relocation** from TQBF to `Build/CfgRecord.lean`, after C1d.
3. **`recordStepTM`'s contract form:** first-return with a bound (recommended),
   or an exact closed form.
4. **`PATH` hardness engine:** ARM (as sketched) or TM record rows with space
   clauses.
5. **Fold and seek in Catalog** (one trace family, after G1), or in `Scan` now
   with their own private skeleton. The latter is faster, but it is a second
   trace of the R3 forward pass.
6. **EmitIterBody dedup** onto `inputCopyTM` in 12.2c T2 (coordinate with
   Aparna).

#### Decisions 12.8.1–12.8.6 (2026-10-10)

1. **Rich-alphabet records** (user): multi-track record cells, mark moves as
   G2 mapped sweeps, and Bool counter rows on rich tapes through **one new
   embedding transport**. Finished by `alphabet_reduction` and
   `alphabet_reduction_spaceUsed`. The maintainer's alternative below is
   adopted, and the binary plan above is superseded where they differ.
2. **`Cfg.InWindow` moves** verbatim to `Build/CfgRecord.lean` after C1d
   (default).
3. **`recordStepTM` has a first-return contract with a bound** (default).
4. **`PATH`-hardness stays on the ARM engine**, as audited (default). The
   record-row route remains an option.
5. **Fold and seek live in Catalog, after the G1 gate** (user), sharing the
   R3/G2 trace, one trace per routine family.
6. **EmitIterBody's private input-copy startup is re-derived** from the new
   input rows in 12.2c T2, with the ch7 owner (default).

**Next.** A revised statement draft for the rich design. What can start
now: the embedding transport and the alphabet-generic input and
constant-write rows. The record rows, fold and seek wait for G1 and G2.

#### Maintainer's alternative for 12.8.1: rich-alphabet records through one embedding transport

Records could follow the §13d pattern instead of being bit-coded. Each record
cell is one rich symbol with tracks (content `Option Bool`, head mark, field
separators), as in the G3 `ZoneCell` carrier. Moving a head mark is then a G2
mapped sweep on one track, and no per-tape `markShiftTM` is needed. Fields
compare through the generic framed compare, and folds read one symbol per
cell.

The binary rows (`incrementTM`, `decrementTM`, `counterLoopTM`, the compare
contracts) need not be generalized. **One new transport lemma** runs them on
rich tapes: the embedding analogue of §12.7's `mapWorkSymbols`, which lifts a
`Bool` machine along `e : Bool ↪ Γ`. Its contract holds from configurations
whose work cells all lie in the image of `e` or are blank, which a dedicated
counter tape satisfies.

The simulator is finished by `alphabet_reduction` for time and by
`alphabet_reduction_spaceUsed` for space (space at most `(N+1)·space + k`).
The latter keeps Savitch and the space hierarchy within their bounds. The
input-position field stays binary over designated digits, so record length
stays `O(k·s + log n + |Q|)`.

The cost is the transport lemma, and records that wait for G2's mapped sweeps
(after the G1 gate). The gain is that the record machines become compositions
of generic rows instead of bit-group machines, and §12.8 and §13d share one
multi-track discipline.


### 12.8a Statement draft for the rich-alphabet design (2026-10-10)

*Recorded from the S1 agent's draft. Its probe is `audits/evidence/s12-8/S128StatementsProbe.lean.txt`; run by the maintainer against the G1 side-branch tree it gives 0 errors and 12 sorry warnings, one per statement left to the fill. Maintainer decisions O1, O4, O5, O6 and the user's O2, O3, O7 are recorded at the end (§8).*

*Landed as statements on 2026-10-11, branch `integrate/s12-8-statements`: §8 lists the landed names, which supersede the draft's below where they differ, the changes from the draft, the R8.0b target signatures, and the open questions for the statement gate.*

*Draft for the statement phase, 2026-10-10. Base: campaign `19964447`; G1 side branch `s13d/g1`
(`10c2c08d`, PR #15, awaiting its gate).*

**Probe.** `drafts/s12-8-probe.lean`, with its output in `s12-8-probe.out`. It contains the
exact Lean of everything below.

- Against the G1 tree (`tools/leanprobe-g1.sh`): **0 errors, 0 warnings other than 12
  `declaration uses 'sorry'`**, one per proposed statement whose proof is fill work.
- Part A, the transport, is fully proved and also elaborates at the campaign HEAD
  (`tools/leanprobe.sh`, extracted as `s1work/p8/partA-head.lean`): 0 errors, 0 warnings.
- Every exact time below that the probe could execute was checked by `decide` on concrete
  configurations (§12.6 practice). That covers seek, the constant writer, the scan with a
  mark-shift instance, the input copier, and the framed compare at displaced heads.

#### 0. What the rich design needs, and the one gap in the decision as worded

Decision 12.8.1 adopts rich record cells, with the `Bool` counter rows run on rich tapes
through one embedding transport. The transport (R8.0) does what was asked:

- it lifts **any** `Bool` machine along `e : Bool ↪ Γ`;
- the lifted increment and decrement rows run on a dedicated digit tape inside a rich host,
  through G1's generic R1 (Part B of the probe).

**It cannot lift a loop with a rich body.** `counterLoopTM M` requires
`M : MultiTapeTM k Bool S`, so lifting it only serves `Bool` bodies. S1b's BFS round, Savitch's
frame step and every record row have rich bodies. After G1, no loop host exists over a
non-`Bool` alphabet. Decision 13d.7 generalized only Seam, Embed, `bufferTape` and the R3
sweeps. It deferred the loop hosts "only when a large-alphabet consumer needs them", and
§12.8's records are that consumer.

The rich design therefore needs **R8.0b, `counterLoopTMVia`**, a counter loop over any
alphabet:

- the body runs through R1 on the first `k` tapes;
- the counter is a dedicated last tape of digits `e b`, decremented by the lifted
  `decrementTM 1 0`, also through R1.

No new trace is needed. The existing round induction is generalized in place, and the
`Bool` contracts are re-derived from the generic ones: at `e = Function.Embedding.refl Bool`
the two tables agree, so Z5's `MultiTapeTM.runFrom_eq_of_agreeOn` transfers. This is the one
substantive addition to the decision; see §5 for its sequencing.

Two smaller findings:

- **The tag type.** `alphabet_reduction` needs `[Fintype Γ]`, and
  `Γ = RecSym N.State T` is `Fintype` only when `T` is. `Turing.OutSummary`, which is frozen,
  derives only `DecidableEq`. So S1b uses `T := Fin 3` through a code of the summary, as S1a's
  private counting already does, or sanctions a `Fintype OutSummary` export. Open decision O4.
- **Space on foreign inputs.** `alphabet_reduction_spaceUsed` hypothesizes
  `∀ x : List Γ, ∀ t, spaceUsed ≤ S |x|`, that is, over **all** rich inputs, including
  non-`Bool` ones. A lifted `Bool` machine reads a foreign symbol as a blank (`decodeBool`), so
  its space on such inputs is not controlled. Every rich space-bounded simulator (Savitch, the
  space hierarchy) must therefore start with a native **input validation fold**, R8.5d, and stop
  on a foreign symbol.

#### 1. R8.0 — the embedding transport

**Home: a new low file `TuringMachine/SymbolLift.lean`, importing `TuringMachine/Finite`.**
The alternative was CounterLoop's `SymbolTransport` section. The transport uses only
`Configuration`/`Deterministic`/`Finite`, and it has consumers below `Build/`: the G3 carrier
(`ZoneSym := Bool ⊕ …` with `e := Sum.inl`) and the Robustness layer. A low home also keeps it
out of `CounterLoop.lean` while that file's §12.7 fill gate is open.

- **Imports:** `Finite` imports `Deterministic`, which imports `Configuration`. Its up-closure
  contains no `Build/` module, so no cycle is possible.
- **Facade:** the `TuringMachine` facade gains one import.
- `mapWorkSymbols` (CounterLoop) can join it at 12.2c's per-theme split.

**Exact declarations** (verbatim in probe Part A, proved):

```lean
def decodeBool [DecidableEq Γ] (e : Bool ↪ Γ) (γ : Γ) : Option Bool :=
  if γ = e true then some true else if γ = e false then some false else none
@[simp] lemma decodeBool_apply [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) : decodeBool e (e b) = some b
def Action.liftSymbols (e : Bool ↪ Γ) (a : Action k Bool State) : Action k Γ State   -- writes/emission mapped by e
def Cfg.liftSymbols (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) : Cfg k Γ State (x.map e)
  -- state, heads unchanged; inputPos := Fin.cast _ c.inputPos; cells and output mapped by e
def MultiTapeTM.liftSymbols [DecidableEq Γ] (M : MultiTapeTM k Bool State) (e : Bool ↪ Γ) :
    MultiTapeTM k Γ State   -- reads through decodeBool e, writes through e
theorem MultiTapeTM.liftSymbols_runFrom [DecidableEq Γ] (M) (e) {x} (c : Cfg k Bool State x) (t : ℕ) :
    (M.liftSymbols e).runFrom (c.liftSymbols e) t = (M.runFrom c t).liftSymbols e
lemma MultiTapeTM.liftSymbols_initCfg : (M.liftSymbols e).initCfg (x.map e) = (M.initCfg x).liftSymbols e
lemma MultiTapeTM.liftSymbols_spaceUsed : (M.liftSymbols e).spaceUsed (c.liftSymbols e) t = M.spaceUsed c t
@[simp] lemma Cfg.liftSymbols_state, Cfg.liftSymbols_workTapePos   -- rfl
lemma Cfg.liftSymbols_inputSymbol : (c.liftSymbols e).inputSymbol = c.inputSymbol.map e
def FinTM.liftSymbols {Γ : Type} [DecidableEq Γ] (M : FinTM Bool) (e : Bool ↪ Γ) : FinTM Γ
theorem FinTM.liftSymbols_computesFunInTimeVia (h : M.ComputesFunInTime f T) :
    (M.liftSymbols e).ComputesFunInTimeVia e f T
```

The one-step lemma `MultiTapeTM.liftSymbols_step`, and `moveInputPos_cast`, are `private` in
the real file.

**Proof notes.**

- `MultiTapeTM.runFrom_comm_of_step` (vendored `Deterministic.lean`) is single-alphabet, so the
  run lemma is a direct induction with `runFrom_succ_eq_step`.
- The one-step lemma decodes the input symbol through
  `Cfg.liftSymbols_inputSymbol`, which needs `Fin.cast` care on the boundary tests.
- The work reads decode by `decodeBool_apply`. Writes commute with `Function.update`.
- The output is `(Option.map e o).toList = o.toList.map e`.

**Corollaries after the G1 merge** (probe Part B, proved). These touch no G1 file:

- `FinTM.bufferTape_map (e) (w) (p) : bufferTape (w.map e) p = (bufferTape w p).map e`. It lives
  in `SymbolLift.lean`, which then imports `Simulation`.
- **Framed lifted rows are one-line consequences.** The probe proves the increment success case:
  `((incrementTM k i).liftSymbols e).runFrom (d.liftSymbols e) (2p+2) = (finish).liftSymbols e`.
  So no per-row lifted statement is proposed; consumers rewrite with
  `liftSymbols_runFrom` and cite the `Bool` row.
- **Dedicated digit tape inside a rich host:**
  `(embedEmitTM ι ((incrementTM 1 0).liftSymbols e)).runFrom (embedEmitCfg ι tapes heads pre
  (d.liftSymbols e)) t = embedEmitCfg ι tapes heads pre ((… .runFrom d t).liftSymbols e)`. The
  host's other tapes (rich records) are R1's frame, so the transport's in-range hypothesis is
  only about the dedicated tape. This is the "dedicated counter tape" discipline of decision
  12.8.1, in usable form.

**Finishing.** Two cases:

- **Time.** A rich decider `D : FinTM Γ` with
  `D.ComputesFunInTimeVia e (fun x => [indicator L x]) T` becomes `FinTM Bool` by
  `FinTM.alphabet_reduction e D f T`, which gives `∃ c M', M'.ComputesFunInTime f (c·(T+1))`.
  The constructor and every `Bool` subroutine enter `D` as `FinTM.liftSymbols` /
  `MultiTapeTM.liftSymbols`, with unchanged time (`liftSymbols_computesFunInTimeVia`) and space
  (`liftSymbols_spaceUsed`).
- **Space.** Use `alphabet_reduction_spaceUsed`, subject to the foreign-input caveat of §0.

##### R8.0b — `counterLoopTMVia`, the counter loop over any alphabet

**Home:** `Build/CounterLoop.lean`. **When:** after the G1 gate (it needs generic
`embedEmitTM`/`embedEmitCfg`) **and** after the §12.7 fill gate. The probe's Part E has the
exact text.

```lean
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1)
def counterLoopTMVia {k} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) : MultiTapeTM (k + 1) Γ (CounterLoopState S)
  -- .body s : (embedEmitTM Fin.castSuccEmb M) redirected by counterLoopRedirect a exit
  -- .dec f  : (embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)) redirected by counterLoopDecExit a
  -- .done / .escape stationary
theorem counterLoopTMVia_run_done   -- counterLoopTM_run_done verbatim with Bool ↦ Γ, plus:
    (hw : ∀ p, -1 ≤ p → p ≤ |w| → ct (cp + p) = bufferTape (w.map e) p)   -- w : List Bool
    -- finish counter cells: `some (e true)`; time `Σ τ + counterOverhead w (d+1)` (unchanged)
theorem counterLoopTMVia_run_escape -- counterLoopTM_run_escape likewise; counter
    -- `bufferTape ((counterWord w (r₀+1)).map e)`
```

- **In-place generalizations (types only, bodies verbatim, G1 rule 2):** `counterLoopCfg` and
  `counterLoopOrbit` become `{Symbol : Type}`. The probe states them as `…Via` copies only to
  avoid a clash.
- `counterLoopTM`, its definition and all `Bool` statements stay byte-identical. Their **proof
  bodies** are swapped to instantiate the generic contracts. The route is
  `runFrom_eq_of_agreeOn` between `counterLoopTM M a exit` and
  `counterLoopTMVia (Function.Embedding.refl Bool) M a exit`. Their dec-phase tables agree
  pointwise (`decodeBool refl γ = some γ`, `Option.map refl = id`, and R1's single-tape action
  equals `decrementTM (k+1) (Fin.last k)`'s), and the other phases agree definitionally.
- **One round induction; net private count down.** `counterLoop_time_le` and the counter
  arithmetic are alphabet-free and reused as they are.

#### 2. The record carrier — `Build/CfgRecord.lean`

**Imports:** `Build/CounterLoop` (for R8.0b) and `TuringMachine/SymbolLift`. **No
`SpaceComplexity` import:** injectivity is stated componentwise rather than through
`ConfigCount.core`, and ConfigGraph converts. **When:** after the G1 merge, since `fieldsTape`
uses generic `bufferTape`. The window predicate lands with the 12.8.2 relocation (after C1d).
The probe's Part F has the exact text.

```lean
inductive RecSym (Q T : Type) where
  | digit (b : Bool)                          -- the `e` of the lift: input, position field, counters
  | cell (content : Option Bool) (mark : Bool)-- one simulated work cell: content track + head-mark track
  | st (q : Option Q)                         -- the state cell
  | tag (τ : T)                               -- the tag cell (emission summary)
deriving DecidableEq
instance recSymFintype (Q T : Type) [Fintype Q] [Fintype T] : Fintype (RecSym Q T) := derive_fintype% _
def RecSym.digitEmb (Q T : Type) : Bool ↪ RecSym Q T
def binDigits (w v : ℕ) : List Bool := (List.range w).map v.testBit       -- little-endian, fixed width
def posWidth (n : ℕ) : ℕ := (Nat.bits (n + 1)).length                      -- 2 ^ posWidth n > n + 1
def cfgRecord {k Q T} {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T) : List (List (RecSym Q T)) :=
  [RecSym.st c.state] ::                                                     -- F0
  ((binDigits (posWidth x.length) c.inputPos.val).map RecSym.digit) ::       -- F1, binary over digits
  (((List.finRange k).map fun i => (List.range (2 * s + 1)).map fun j =>     -- F2 … F(k+1)
      RecSym.cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s))) ++
  [[RecSym.tag τ]])                                                          -- F(k+2)
def joinFields (fs : List (List Γ)) : List (Option Γ) := List.intercalate [none] (fs.map (List.map some))
def fieldsTape (fs : List (List Γ)) (z : ℤ) : Option Γ := if 0 ≤ z then ((joinFields fs)[z.toNat]?).join else none
def fieldOffset (fs : List (List Γ)) (j : ℕ) : ℕ := ((fs.take j).map (·.length + 1)).sum
theorem fieldsTape_field (fs) (j) (hj : j < fs.length) : ∀ p, -1 ≤ p → p ≤ |fs[j]| →
    fieldsTape fs (fieldOffset fs j + p) = FinTM.bufferTape fs[j] p   -- each field is a framed word
theorem cfgRecord_inj (s) (hc : c.InWindow s) (hd : d.InWindow s) :
    cfgRecord s c τ = cfgRecord s d τ' ↔
      (c.state = d.state ∧ c.inputPos = d.inputPos ∧ c.workTapes = d.workTapes ∧
        c.workTapePos = d.workTapePos) ∧ τ = τ'
theorem cfgRecord_length : (cfgRecord s c τ).length = k + 3   -- proved in the probe
def RecordValid (k n s : ℕ) (Q T) (fs) : Prop :=
  ∃ x (c : Cfg k Bool Q x) τ, x.length = n ∧ c.InWindow s ∧ cfgRecord s c τ = fs
theorem recordValid_iff (n s fs) : RecordValid k n s Q T fs ↔ fs.length = k + 3 ∧ (∃ q, fs[0] = [.st q]) ∧
    (fs[1] is posWidth n digits of value ≤ n + 1) ∧ (each tape field: 2s+1 `.cell`s, exactly one mark) ∧
    (∃ τ, fs[k+2] = [.tag τ])            -- the scan-checkable form, for `recordValidTM`
def RecordAt (d : Cfg K Γ S x) (r : Fin K) (fs) : Prop :=
  ∀ p, -1 ≤ p → p ≤ |joinFields fs| → d.workTapes r (d.workTapePos r + p) = fieldsTape fs p
```

- **Layout discipline.** One blank between fields and between records; no field is empty (F0
  and the tag have one cell, F1 has `posWidth n ≥ 1` cells, each tape field `2s+1` cells). So
  two consecutive blanks mark the end of a table, and every field is a §12.6-delimited word.
  This is the G3 separator discipline, so the generic framed rows apply field by field with no
  save/restore.
- **Space.** A record has `k(2s+1) + posWidth n + 2` cells plus `k + 2` separators, which is
  `O(k·s + log n + 1)`. That is `O(S n)` at `s = c₀·S n` with `S ≥ logSpace`. With
  `alphabet_reduction_spaceUsed`'s `c·(space+1)`, Savitch stays in `SPACE(S²)`.
- **Window predicate.** The probe uses `WindowedP`, a verbatim copy of TQBF's
  `Turing.Cfg.InWindow`. The real file uses `Cfg.InWindow`, relocated here (12.8.2). It **must
  land in the same change** that deletes TQBF's copy: once ConfigGraph imports `CfgRecord` (at
  S1b), TQBF, which is downstream, would otherwise see two definitions.

#### 3. The rows, restated for the rich design

Template (from the §12.8 note), with one change of form:

- **Machines that are single sweeps are defined** and get the §12.6 framed contract: exact
  time, finish configuration, no earlier exit, trajectory.
- **Composite modules are existential**, in the `exists_installCallTM` style
  (`∃ R entry exit C, …`): a first-return time `t ≤ C·(size)`, no earlier exit, an exact finish
  configuration, and the scratch tapes and heads restored.

The constants are indicative; the statement phase fixes them by execution. Tags: **[now]**
can land on the campaign branch before G1 merges. **[G1-merge]** touches no G1 file but uses
G1's generic statements. **[Catalog/G1]** goes in a G1-owned file, after the G1 gate. **[G2]**
is proposed as a G2 statement. **[rec]** is a record row, filled after G2 and the
Catalog/G1 rows.

| Row | Tag | Statement (probe part) | Contract |
|---|---|---|---|
| **R8.0** transport | **[now]** | `MultiTapeTM.liftSymbols_runFrom` and the rest of §1 (A) | proved |
| R8.0 corollaries | [G1-merge] | `FinTM.bufferTape_map`; the R1 composition (B) | proved |
| **R8.0b** `counterLoopTMVia` | [Catalog/G1]+§12.7 gate (CounterLoop) | `counterLoopTMVia_run_done/_escape` (E) | exact, as §12.7 |
| **R8.1** framed compare | [Catalog/G1] | `compareTM_run_ofCfg {Symbol} [DecidableEq Symbol]` (D) | `∃ δ ≤ min |u| |v|`, exact time `2δ+2`, finish `{d with state := done (decide (u = v))}`, no earlier verdict, trajectory `[pos−1, pos+δ]`. Canonical `compareTM_run` re-derived (body swap); the trace generalizes `catalog_compare_trace` |
| **R8.2** `scanTM δf δb a₀` (two-pass transducer) | **[G2]** | `scanTM_run_ofCfg` (D) | exact `2|w|+2`; interval rewritten to `(scanResult δf δb a₀ w).2`, verdict `done (scanResult …).1`; trajectory `[pos−1, pos+|w|]` |
| **R8.3** `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM` | [Catalog/G1] | `skipTM_run_ofCfg` (D); landed with `skipBackTM_run_ofCfg`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg` | skip: exact `|w|+1`, head to `pos+|w|+1`. Landed: skip back is skip's inverse, exact `|u|+3` from the next field's first cell to `u`'s; seek end exact `D+1` to `pos+D`, `D = fieldOffset ws |ws|`, `ws ≠ []`; seek start exact `D+4` back to the table start. Nothing written; the seeks stop at two consecutive blanks (table ends) |
| **R8.4** `writeConstTM i w₀` | [G1-merge] (Scan) | `writeConstTM_run_ofCfg` (C) | exact `2|w₀|+2` (executed), old contents arbitrary, head returns |
| R8.4′ `writeAdvTM i w₀` | [G1-merge] (Scan) | landed: `writeAdvTM_run_ofCfg` | writes `w₀` and leaves the head at `pos + |w₀|`, exact `|w₀| + 1`; the advancing round of `expandTM`. Landed cyclic, over `Fin (|w₀|+1)`: it returns to its start state `0`, the counter-loop round shape |
| **R8.5a** `inputCopyTM i` | [G1-merge] (Scan) | `inputCopyTM_run_ofCfg` (C) | from input position 1, exact `2|x|+2` (executed); both heads return in lockstep (no left delimiter needed) |
| **R8.5b** `exists_inputSeekTM` (`Bool`) | **[now]** | (C) | `∃ R … C`; moves the input head to the binary value on a dedicated tape, `t ≤ C·(|w| + pos + p + 1)`; tapes restored |
| **R8.5c** `exists_inputLengthTM` (`Bool`) | statement now; fill after R8.3 (it needs `skipTM` for the width extension) | — | writes `Nat.bits |x|` on a dedicated tape: per input symbol, `incrementTM` with width extension on overflow (`seekEnd` + `writeConst`), `t ≤ C·(|x|+1)` amortized (§12.7 potential) |
| **R8.5d** `inputFoldTM δ a₀` | [G1-merge] (Scan) | — | native scan of the input with a finite fold, verdict `done (x.foldl δ a₀)`, exact `2|x|+2`; the foreign-symbol validator of §0 |
| **R8.5e** `exists_inputCallTM` | [G1-merge] (`Build/InputCall.lean`; needs R8.5a) | — | `inputCopyTM` (at `Bool`, or lifted) + `exists_installCallTM`: a function-level machine on the native input at a clean seam |
| **R8.6** `exists_expandTM pat` (`Bool`); landed as the definition `expandTM` | [G1-merge] (CounterLoop; needs R8.4′) | landed: `expandTM_run_ofCfg` | `counterLoopTM` round = `writeAdvTM pat`; writes `pat` `d` times contiguously; exact `d(|pat|+1) + counterOverhead w (d+1)` |
| **R8.7** record rows | **[rec]** | `exists_recordStepTM`, `exists_recordEqTM` (G); landed with `exists_recordTestTM`; the rest below | first-return form; landed with `yes ≠ no` in each existential |
| **R8.8** `seamCompTM_runFrom_left` (promotion) + `seamCompTM₂_run_ofCfg` | [Catalog/G1] (Seam) | §12.8 note | statement unchanged from the private `seamComp_left` |

**R8.2 replaces fold, map, mark shift and odometer: one row, one trace.** It is proposed **as a
G2 statement**. Its instances:

- **fold:** `δf a γ := (δ a γ, γ)`, `δb` the identity;
- **in-place map** `f`: `δf a γ := (a, f γ)`;
- **head-mark shift right:** `δf prev γ := (mark γ, setMark γ prev)`, the forward delay (the probe
  checks a concrete shift);
- **shift left:** the same delay on the backward pass;
- **record odometer:** a carry transducer;
- **validity checks:** folds.

G2's planned two-tape `copyMapTM`/`transferMapTM` (§13d) are not needed by §12.8: records move
by plain generic `copyTM`. If G2 keeps them, one request: let `merge` take `Option Γ`, so that
blank destinations (scratch) are admitted. **Decision 12.8.5 is honored:** fold, and with it map,
is a Catalog row sharing the R3/G2 trace (`catalog_trace_run`), since G2 lives in Catalog.

**R8.7, the record rows.**

- All are existential modules over `RecSym Q T`.
- **Entry conditions:** the record at tape `0` (`RecordAt`), the scratch tapes `j ≠ 0` blank,
  and the native input `x.map RecSym.digitEmb`.
- **Exit conditions:** heads, input position, scratch and output restored.
- They are built from R8.0/R8.0b, R8.1–R8.5 and R2 seams, with **no private re-trace**.

| Module | Verdict / effect | Composition |
|---|---|---|
| `exists_recordStepTM M upd (hupd : ∀ τ, upd τ none = τ)` (GAP-4, exact text in G) | `yes` and record of `M.step c` with tag `upd τ (M.outputSymbol c)` if `(M.step c).InWindow s`; else `no`, nothing changed; `t ≤ C·(L + |x| + 1)` | read: `scanTM` folds on F0, the tag and the tape fields (scanned symbols and edge flags) via `skipTM`; copy F1 to a dedicated digit tape (`copyTM`), run the lifted `inputSeekTM`, read the input symbol, restore; finite dispatch on `M.tr`; apply: `scanTM` maps (content at the mark, F0, tag) and delay shifts (marks), F1 `±1` by the lifted increment/decrement on the dedicated tape with copy back, clamp from the edge data |
| `exists_recordEqTM` (G) | `yes` iff the two field lists are equal | `k+3` framed compares (R8.1) with `skipTM`s |
| `exists_recordTestTM P` | `P (state, tag)` | two `scanTM` folds |
| `exists_recordValidTM` | `RecordValid` via `recordValid_iff` | `scanTM` folds per field |
| `exists_recordInitTM` | writes `cfgRecord s (initCfg x) τ₀` from `bits (S n)`-style radius digits | `exists_inputLengthTM` (lifted), `exists_expandTM` (lifted) for the window halves, `scanTM` maps, `writeConstTM` |
| `exists_recordNextTM` | next valid record in odometer order, or overflow | `scanTM` carry over all fields + `exists_recordValidTM` filter, under `counterLoopTMVia` |
| `exists_tableAppendTM`, `exists_tableFindTM P` | append at `seekEndTM`; first record satisfying a fold, with an escape if none | `copyTM`, `seekEndTM`, `scanTM`, `counterLoopTMVia` |

#### 4. S1b's machine plan, recomposed (rich)

**Parameters.** `Γ := RecSym N.State (Fin 3)`, with the tag being the output summary through
its `Fin 3` code (O4), and `e := RecSym.digitEmb`. The host is a `FinTM Γ`.

**Tapes:**

- `Tab`, the table;
- `Cur₀` and `Cur₁`, the successor workspaces;
- scratch for the record modules;
- dedicated digit tapes: `Rad` (radius), `Len`, `Cnt` (the outer counter, last tape) and
  `Cnt'` (inner loops);
- the lifted constructor's bank and capture tape.

1. **Validate** with `inputFoldTM`. On a foreign symbol, emit `e false` and halt. This is needed
   only for space, but it is cheap.
2. **Radius.** Run `M_S.liftSymbols e` under generic `embedSilentRetTM` with its output
   captured on `Rad`, then rewind. Time at most `M_S.configBound n (a·S n)`
   (`of_spaceUsed_le` plus `liftSymbols_runFrom`).
3. **Window template.**
   - Lifted `exists_expandTM` with counter `bits (S n)` and pattern `false^{c₀}` writes the left
     half.
   - `writeConstTM [.cell none true]` writes the center.
   - `expandTM` again writes the right half.
   - A `scanTM` map turns the digits into `.cell none false`.

   No multiplication by `c₀` is needed: the pattern length carries it.
4. **Initial record.** `exists_recordInitTM` writes it, plus a one-digit flag field `[digit
   false]` ("unprocessed").
5. **Outer counter.** Copy the template fields `c_N` times onto `Cnt` (`copyTM` + `skipTM`),
   then map every cell to `digit true` (`scanTM`). Its value `2^{c_N·W} − 1` exceeds the record
   count `V` with `c_N := ⌈log₂(3(|Q|+1))⌉ + 4`. Here `W` is the record's cell count, and the
   proof uses `2^{posWidth n} ≥ n+2` and `8^{2s+1} ≥ 3^{2s+1}(2s+1)`.
6. **BFS** with `counterLoopTMVia e Round a (some ex)`. A round:
   - `exists_tableFindTM` finds the first record with flag `false` (escaping to `ex` if none),
     and copies it to `Cur₀` and `Cur₁`;
   - `exists_recordStepTM (N.fixChoice false)` runs on `Cur₀`, and
     `exists_recordStepTM (N.fixChoice true)` on `Cur₁`. The upd is the summary's append table
     on the code;
   - for each `yes`, an inner `counterLoopTMVia` over the table with `exists_recordEqTM`
     decides membership, and `exists_tableAppendTM` appends a new record with flag `false`;
   - the processed record's flag is set (`scanTM` map), the workspaces are cleared
     (`clearTM`), and the table head is rewound (`seekStartTM`).

   Both exits are wired by R8.8.
7. **Verdict.** `exists_tableFindTM (accept)` scans for a record with state `none` and tag
   `accept`. Emit `e true` or `e false`, then halt.
8. **Finish.** `alphabet_reduction` gives a `FinTM Bool` within `c·(T + 1)`.
9. **Correctness** is §12.8's chain, with `cfgRecord_inj` in place of the bit codec:
   - `T := Fin 3` identifies records with `coreSum`s;
   - note-6's bridge applies, the outside-window rejection being `recordStepTM`'s `no`;
   - S1a's four lemmas finish.
10. **Time.**
    - `counterLoop_time_le` gives `V·B + 4V + 2|w| + 2`, with `B = O(V·(L+F) + n)` from the
      nested table loop.
    - Add the startup terms: the constructor bound, `O(S n)`-cost expansions, and
      `O(n log n)` input length.
    - Then `alphabet_reduction`'s `c(T+1)`. The result is at most `K·2^{c'(S n+1)}`.
    - Every budget is evaluated at `n`; no monotonicity of `S` is used.

#### 5. Sequencing — what can be issued before the G1 gate closes

| Item | Lands | Blocked on |
|---|---|---|
| **R8.0 transport** (`SymbolLift.lean`) | **now**. The probe's Part A *is* the proof; a maintainer pre-issue landing or a tiny batch | nothing |
| **R8.5b** `exists_inputSeekTM` (`Bool`; composed of `copyTM`, `timed_rewind`, `counterLoopTM`, `clearTM`, all public at HEAD) | **now**, as a statement phase plus a fill batch | nothing; it lifts to rich hosts by R8.0 |
| R8.5c, R8.5e, R8.6 (`Bool` rows needing Scan or seek) | statements now; fills after the G1 merge (R8.5e, R8.6) or after R8.3 (R8.5c) | G1 merge / R8.3 |
| Statements of **everything else** | **draft now** (this document, probe green on `s13d/g1`) | — |
| R8.0 corollaries, R8.4, R8.5a/d, the `CfgRecord` pure layer | after **G1 merges** (no G1 file edited) | G1 gate; CfgRecord's `InWindow` also on C1d |
| R8.1, R8.3, R8.8 | after the **G1 gate**, in Catalog/Seam | G1 gate; coordinate with G2/G4 (one trace) |
| R8.2 `scanTM` | with **G2** | G1 gate; G2's statement phase adopts it |
| **R8.0b** `counterLoopTMVia` | after the **G1 gate and the §12.7 fill gate** | both gates |
| R8.7 record rows | after the R8.2 fill (G2) and the R8.1/R8.3 fills | G2 fill |
| S1b | after R8.7 | — |

**The sequencing change versus the note:** R8.0b is new, and it sits on two gates (G1, §12.7).
It is the long pole for every rich consumer, since no rich loop exists without it. Some things
can be issued before the G1 gate closes:

- R8.0, which the probe proves;
- R8.5b;
- the statement phase of every other row (the probe is green on `s13d/g1`).

The critical path is then the G1 gate, then R8.0b with R8.2 (G2) and R8.1/R8.3, then R8.7,
then S1b. Two items that the note called "landable now" in fact need the G1 merge, because
their statements use the generic `bufferTape`: `writeConstTM` and the input rows. `expandTM`
needs the advancing writer R8.4′.

#### 6. Per-consumer rows (updated)

| Consumer | Rows |
|---|---|
| **S1b** | §4: R8.0, R8.0b, R8.1–R8.5, R8.6, R8.7 (step, eq, test, init, table rows), R8.8, `alphabet_reduction` |
| **Savitch** | Rich records with binary F1 (`O(S)` cells); frame stack on a rich tape; R8.7 `recordStepTM` (both choice bits) + `recordEqTM` for adjacency; `recordNextTM` + `recordValidTM` for midpoints; R8.3 over frames; `copyTM`/`clearTM` at fixed intervals (note 7); R8.0b loops; R8.8; R8.5d validation; `alphabet_reduction_spaceUsed` |
| `spaceConstructible_*` | `Bool` only: R8.5c, R8.6, `incrementTM` |
| `PATH_NLComplete` (hardness) | ARM engine (12.8.4); no §12.8 row |
| `PATH_mem_NL` | R8.5b, once the nondeterministic host exists (SC-3) |
| Space hierarchy | `Bool` counters lifted by R8.0 on a rich simulator, or unlifted on a `Bool` one; R8.0b (budget loop), R8.8 (success/cap), R8.1 (budget comparison), `clearTM` resets, R8.5d. It simulates a coded machine, so it does not use R8.7 |
| `TQBF_mem_PSPACE` | R8.2 (validation folds, clause evaluation, the trit odometer), R8.5b (input re-reads), R8.3 |
| `NP_subset_PSPACE` | `incrementTM`, `vhostEmitTM`, R8.8 |
| **G3/G4 (§13d)** | R8.3 (zone scanning across separators), R8.2 (per-track maps), R8.0 (Bool counters on `ZoneSym` tapes via `e := Sum.inl`) |

#### 7. Open decisions

- **O1, transport home.** New `TuringMachine/SymbolLift.lean` (recommended), or CounterLoop's
  `SymbolTransport` section (during its open gate).
- **O2, R8.0b route.** In-place proof generalization with the `Bool` contracts re-derived by Z5
  (recommended; one round induction). The alternative is a second host with its own induction,
  which is a duplicated trace.
- **O3, `scanTM` as a G2 statement.** It needs G2's agreement. Separately, the optional
  `merge : Option Γ → Δ → Γ` request for `copyMapTM`.
- **O4, the S1b tag type.** `Fin 3` code (recommended; no frozen-surface change), or a sanctioned
  `Fintype OutSummary` export in ConfigGraph.
- **O5, table seeks.** `seekEndTM` and `seekStartTM` (double-blank stops) in the skip family, or
  as `counterLoopTMVia` loops over `skipTM` (slower, no new row).
- **O6, input validation (R8.5d).** Mandatory for rich space-bounded consumers. Confirm, or
  require every rich row's space bound to be input-independent instead (harder to state).
- **O7, R8.0 now.** Whether the transport lands as a maintainer pre-issue lemma, since the
  probe proof is complete (one file, about 120 lines), or through a statement gate plus fill
  like the other §12 rows.

#### 8. Decisions and the landed statement layer (2026-10-11)

**Decisions.**

- **User:** O2, generalize `counterLoopTM` in place, with the `Bool` contracts
  re-derived by Z5 (R8.0b, a later batch; target signatures below); O3, G2 is
  `scanTM`; O7, the transport lands by PR plus the §12.8 statement gate.
- **Maintainer:** O1, `TuringMachine/SymbolLift.lean` (landed, PR #16); O4, the
  `Fin 3` tag code; O5, dedicated `seekEndTM`/`seekStartTM` rows; O6, input
  validation (R8.5d) is mandatory for rich space-bounded consumers.

**Landed** on `integrate/s12-8-statements` (campaign `5e438f50` with PR #16,
merged at `b28e22ea`). Every machine and carrier is a real definition. Every
contract is sorried with a proof sketch, except the two results already
proved, which keep their proofs: `seamCompTM_runFrom_left`, promoted verbatim,
and `cfgRecord_length`. There are 25 new sorries. Records:
`audits/logs/s12-8-statements-*` and
`audits/evidence/s12-8/S128StatementsPreship.lean.txt`.

| Row | File | Landed declarations | Contract |
|---|---|---|---|
| one-tape actions | `Build/Catalog.lean`, Part 3 | `tapeAction`, `inputMoveAction` | the transition-table vocabulary of every §12.8 machine |
| field layout | Catalog, Part 3 | `joinFields`, `fieldsTape`, `fieldOffset`, `fieldsTape_field` | each field is a §12.6 delimited word in place |
| R8.1 | Catalog, Part 3 | `compareTM_run_ofCfg` | as drafted |
| R8.3 | Catalog, Part 3 | `SeekPhase`; `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM`, each with `_run_ofCfg` | as in the §3 row, with trajectories |
| R8.2, the G2 core | Catalog, Part 3 | `mealyRun`, `scanResult`, `ScanPhase`, `scanTM`, `scanTM_run_ofCfg`; the steps `scanKeep`, `scanFold`, `scanMap`, `scanShift`, `scanCarry`; the identities `scanResult_fold`, `scanResult_map`, `scanResult_shiftRight`, `scanResult_shiftLeft`, `scanResult_carry` | the scan contract as drafted. The instances are pure identities of `scanResult`, so the scan keeps one framed contract |
| R8.4, R8.4′, R8.5a, R8.5d | new `Build/Scan.lean` | `WritePhase`, `writeConstTM`, `writeAdvTM`, `inputCopyTM`, `inputFoldTM`, each with `_run_ofCfg` | constant writer `2|w₀|+2`; advancing writer `|w₀|+1`, cyclic; input copy and input fold `2|x|+2` from input position `1` |
| R8.5e, R8.5b | new `Build/InputCall.lean` | `FinTM.exists_inputCallTM`, `exists_inputSeekTM` | first-return modules |
| R8.6 | `Build/CounterLoop.lean` | `expandTM := counterLoopTM (writeAdvTM k i pat) 0 none`, `expandTM_run_ofCfg` | exact `d(|pat|+1) + counterOverhead w (d+1)`, with `d` copies of `pat` from `pos` |
| R8.7 | new `Build/CfgRecord.lean` | `Cfg.InWindow` (relocated verbatim from `ClassPSPACE/TQBF.lean`, which now imports it); `RecSym`, `recSymFintype`, `RecSym.digitEmb`, `binDigits`, `posWidth`, `cfgRecord`, `cfgRecord_length` (proved), `cfgRecord_inj`, `RecordValid`, `recordValid_iff`, `RecordAt`; `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM` | first-return modules with distinct verdict anchors |
| R8.8 | `Build/Seam.lean` | `seamCompTM_runFrom_left` (promoted), `seamCompTM₂`, `seamCompTM₂_run_ofCfg` | one continuation per exit, each run unboundedly after the dispatch step |

**Changes from the draft.** Each was executed in the pre-ship probe where
executable.

1. **`yes ≠ no`** is part of every record row's existential. Without it, a
   module with `yes = no` satisfies `exists_recordEqTM` vacuously, and no
   consumer could branch on the verdict.
2. **The field layout lives in Catalog**, not in CfgRecord, because the seek
   rows' contracts are stated over it. CfgRecord imports Catalog and
   `SymbolLift`, not CounterLoop, since R8.0b is not in this step. TQBF's
   import closure gains Catalog, `SymbolLift` and CfgRecord; there is no
   cycle.
3. **`writeAdvTM` is cyclic** over `Fin (|w₀|+1)`. It returns to its start state
   `0`, so it is a counter-loop round as it stands. A seam caller that runs it
   once uses `seamReleaseTM`.
4. **R8.6 is the concrete `expandTM`** with an exact contract, not an
   existential.
5. **The seek family.** Skip back is the inverse of skip (`|u|+3`, from the
   next field's first cell), not its mirror. The seeks' exact times are `D+1`
   and `D+4`, with `D = fieldOffset ws |ws|`. Every row carries the §12.6
   trajectory clause.
6. **No new copier phase type.** The input copier reuses `SweepPhase`, and the
   input fold reuses `ScanPhase`.
7. **The scan instances** are stated as identities of `scanResult` rather than
   as five machine contracts. `scanTM_run_ofCfg` turns each into the
   instance's run.
8. **`Cfg.InWindow`** replaces the probe's `WindowedP`.
9. **One-tape actions.** The §12.8 machines' tables are written with two
   named actions, `tapeAction` and `inputMoveAction`, instead of literal
   `Action` tuples. With literal tuples, the copy-text screen found 17 new
   cross-file pairs: the input copier and the input fold against the R3
   sweeps and the scan. With the helpers there are none. Twelve new same-file
   pairs remain: the four seek tables among themselves, and the two writers.
   These are distinct small machines sharing their phases, not copied
   proofs. The proved R3 tables are unchanged.
10. **Not landed**, being outside this step:
    - `FinTM.bufferTape_map` and the other R8.0 corollaries;
    - R8.5c, `exists_inputLengthTM`;
    - R8.0b;
    - the record rows `exists_recordValidTM`, `exists_recordInitTM`,
      `exists_recordNextTM`, `exists_tableAppendTM` and
      `exists_tableFindTM`. Their statements need S1b's table layout (a
      header, the radius digits, the odometer order) and a template tape
      holding the widths a validity machine compares against.
11. **`MultiTapeTM.liftSymbols_step` is public** in the landed
    `SymbolLift.lean` (PR #16), as the transport's one-step form; §1 above
    made it private. Only `moveInputPos_cast` is private.

**R8.0b target signatures.** These land in a later batch, after this
statement gate. Home `Build/CounterLoop.lean`, which then imports
`SymbolLift`.

```lean
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) := ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩
def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) : MultiTapeTM (k + 1) Γ (CounterLoopState S)
  -- .body s : ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
  -- .dec f  : ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
  --             (counterLoopDecExit a)
  -- .done, .escape : stationary
-- generalized in place (types only, bodies verbatim; existing call sites unchanged):
def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol} (q : Option (CounterLoopState S))
    (c : Cfg k Symbol S x) (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x
def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x
theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol} … -- otherwise verbatim
-- the generic contracts are counterLoopTM_run_done / counterLoopTM_run_escape verbatim, with
--   M, τ, c over Γ; ct : ℤ → Option Γ; counterLoopTM M a exit ↦ counterLoopTMVia e M a exit;
--   hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p,
--     for the counter word w : List Bool;
--   done finish counter: fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q;
--   escape finish counter: fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
--     then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q;
--   all four clauses kept (finish, no earlier exit, counter head range, body heads).
theorem counterLoopTMVia_run_done …
theorem counterLoopTMVia_run_escape …
-- counterLoopTM and its two contracts: statements byte-identical; proofs re-derived at
-- e := Function.Embedding.refl Bool through MultiTapeTM.runFrom_eq_of_agreeOn (Z5), the
-- decrement tables agreeing pointwise (decodeBool refl γ = some γ, Option.map refl = id).
```

**Governance.** Catalog and Seam are G1-owned files, and `scanTM` is the G2
core of the §13d revision. Under the §13d rule this branch therefore lands by a
PR the user merges, with its own statement gate. Nothing is pushed by the
agent.

**Open questions for the statement gate.**

1. **Skip back.** Is the inverse convention right (from the next field's
   start, `|u|+3`), or should it be the mirror of skip (from a word's last
   cell, `|u|+1`)?
2. **The empty table.** `seekEndTM` requires `ws ≠ []`, since an empty table's
   end is its start. Should tables carry a header field, so that every seek
   precondition is uniform?
3. **The cyclic writer.** Is `writeAdvTM`'s anchor-equals-start shape
   acceptable, or should it have a stationary `done` with the loop adapting
   it?
4. **Tape layouts of the record rows.** `exists_recordStepTM` has
   `K + 1` existential tapes with the record on tape `0`; `exists_recordEqTM`
   has 2 tapes; `exists_recordTestTM` has 1. Hosts embed them by R1. Is the
   fixed layout acceptable, or should each row take a tape selection? The
   step row's fill will also import InputCall, for the input seek, which
   enlarges TQBF's import closure again.
5. **The deferred record rows.** Should validity, init, next and the table
   rows enter this gate, or S1b's statement phase, once the table layout is
   fixed?
6. **The facade.** Scan, InputCall and CfgRecord are not wired into the
   `TuringMachine` facade, following the precedent of `SymbolLift`,
   CounterLoop and Zone. Is facade wiring wanted at this gate?
7. **G2's agreement** to `scanTM` as its core, and whether the planned
   `copyMapTM`/`transferMapTM` are still wanted. §12.8 does not need them.

#### 9. Statement gate, round 1: decisions and repairs (2026-10-11)

Round 1 failed with 0 blockers, 1 major, 7 minors and 39 notes
(`audits/s12-8-statements-findings.md`).

**Decisions** (user, the auditor's recommendations, on the open questions
of §8):

1. Skip back stays the **inverse** of skip, at `|u| + 3`.
2. Shared tables get a **fixed nonempty header field**, so seek end always
   has a field to stop after. The table ends are two blank cells before the
   header and two after the last field. From seek end's stopping blank, a
   consumer reaches the table start by skipping back over the last field
   and then seeking start. The deferred table rows are stated with this
   layout.
3. `writeAdvTM` stays **cyclic**. One-shot callers use `seamReleaseTM`.
4. The record rows keep their **fixed local tape layouts**, and hosts embed
   them by R1.
5. The deferred record rows (validity, init, next, table append and find)
   get **their own statement gate** with S1b's concrete layout, before
   S1b's fill uses them. R8.0b and R8.5c are explicit prerequisites.
6. The new modules are **wired into the `TuringMachine` facade** at this
   gate: `SymbolLift`, `Build/CounterLoop`, `Build/Scan`, `Build/InputCall`
   and `Build/CfgRecord`. Nine older files of the topic are also absent
   from the facade; they are recorded as `backlog.md` FAC-1.
7. G2's core is `scanTM`, and `copyMapTM`/`transferMapTM` stay for G3/G4
   (§13d, G2).

**Repairs** (for round 2):

- **Major 1: work-space clauses.** The record rows and the input seek
  bounded time but not the cells they visit, so they were too weak for
  Savitch and logspace consumers. Each now bounds every work head, through
  its verdict or exit, to `C·(size + 1)` cells of its entry position. The
  size is the record's layout length for the step and test rows, `fs`'s
  layout length for the equality row, and `|w|` for the seek. So the space
  does not depend on how far the native input head travels, and repeated
  calls compose. The step row's sketch now names the obligations the auditor
  identified: save and restore the host's input position in binary, and
  clamp the position field at `0` and `|x| + 1`.
- **Minor 2.** The input seek's rewind: `timed_rewind` stops at position
  `1` within `pos + 2` steps, and one left move follows.
- **Minor 3.** The input call's first-return clause splits on whether the
  callee's entry equals its exit. If it does, `seamReleaseTM` supplies a
  fresh entry first.
- **Minors 4, 5 and 6.** `recordValid_iff`'s validator needs width
  templates. A record determines the configuration *core* together with the
  tag. `fieldOffset`'s end formula needs `fs ≠ []`.
- **Minors 7 and 8.** Corrected in the records: the declfreeze log
  miscounted the promotion's citations (3, not 4), and Catalog's ledger
  denominator is now 459.

