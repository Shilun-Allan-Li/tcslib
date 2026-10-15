# B6 hosts: design note for the statement gate (H3, its clock, H5, `U₀`, the bridges)

> **Maintainer note (2026-10-13).** A maintainer sub-agent wrote this note and the draft against
> the read-only checkout `wt-b6h` of campaign commit `6aa9f67bc0b3181672d50eacb9d172e468070df3`.
> In the repository, `b6hosts/B6Hosts.lean` is `audits/evidence/b6hosts/B6HostsDraft.lean.txt`,
> `b6hosts/elaboration.log` is `audits/logs/b6-hosts-draft-elaboration.log`, and `c1/`, `h2/`
> and `b6hosts/b6-restatement-findings.md` are `audits/evidence/c1/`, `audits/evidence/h2/` and
> `audits/b6-restatement-findings.md`. The scratch probes in `b6hosts/work/` are not kept.
> Two statements in §6 are out of date: MIG-0a has passed its gate and landed (PR #83), and
> MIG-0b's gate is issued (`audits/mig0b-pack.md`). The line numbers into the design document
> and the backlog are at that commit; the Lean references still hold.

Maintainer draft, 2026-10-13. It concerns cluster B6 on its window route
(`machine-library-design.md` §16b item 3, line 3789; backlog RD-3, `backlog.md:699`). It was
written read-only against the campaign tip checkout `wt-b6h`. Every `file:line` below refers
to that checkout's `TCSlib/Complexity/` unless it names `b6hosts/`, which means this directory.

**Deliverables.**
- `b6hosts/B6Hosts.lean`: 1,406 lines, 55 declarations (MEASURED). It elaborates with
  **0 errors and exactly 10 `sorry` warnings**, one per machine contract, and no other warning
  (`b6hosts/elaboration.log`). All 100-column.
- **Everything that is not a machine contract is proved**: 43 declarations (definitions and
  lemmas), about 330 proof lines (MEASURED, by a script count of proof bodies). A scratch axiom
  probe prints the standard triple for every proved lemma; `sorryAx` appears only in the 10
  contracts and in `space_universal_gated_form`, which is derived from one of them
  (`b6hosts/elaboration.log`, second part).
- This note.

**Requirements met.** The statements answer the RD-3 gate's findings
(`b6hosts/b6-restatement-findings.md`): notes 7–8, rows 1 and 3, the seven numbered checks, and
the four suggested sanity obligations (§7 maps each one). They also answer the coordinator's
cross-consumer request from C1 (`c1/C1-design.md` §3.3): **H3's clock is the step-clocked
runner, stated once as its own contract.** C1 cites it (§5).

Contents:
1. The statements at a glance
2. What each statement provides, and to whom
3. How `space_hierarchy`'s fill uses them
4. How an addend-free `space_universal` would use them, and when to strengthen it
5. The joint clock with C1: what C1 cites
6. Dependencies
7. The auditor's checks and sanity obligations, mapped to statements
8. Proposed homes
9. Size estimates (ESTIMATE)
10. Open questions, each with a recommendation

---

## 1. The statements at a glance

| § | Declaration | Kind | Status |
|---|---|---|---|
| 1 | `MultiTapeTM.relabelState_visitedByTapeHead`, `_spaceUsed` | bridge: relabelling preserves every head trajectory | proved |
| 1 | `exists_codeTM_spaceUsed` | bridge: the space clause of `exists_codeTM` | proved |
| 1 | `CodeTM.one_le_spaceUsed` | every coded run has `s ≥ 1` (row-1 ledger) | proved |
| 1 | `FinTM.ComputesInTime.spaceUsed_le_of_halt` | bridge: halt-time space bound at every time | proved |
| 1 | `FinTM.ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le` | bridge: exactly the normal form's `hM`, `hS` | proved |
| 1 | `FinTM.inWindow_of_spaceUsed_le`, `Cfg.inWindow_init` | window containment (check 6) | proved |
| 1 | `FinTM.decidesInSpace_of_alphabetReduction` | `D`'s packaging through the alphabet reduction (check 7) | proved |
| 2 | `WindowExit`, `windowRun` | H3's semantics: the three exits | definitions |
| 2 | `windowRun_halted_of_run`, `_spec`, `_tag`, `_stop_unique` | H3's semantics: forward halt, full characterization, tag, determinism | proved |
| 2 | `windowRun_exhausted_of_live`, `windowRun_halts_on_last_transition` | sanity: the surplus round is needed, and suffices | proved |
| 2 | `outSummaryCode`, `summaryWord`, `summaryTag`, `summaryTag_none`, `summaryTag_append`, `outSummaryCode_eq_one_iff`, `outSummaryCode_nil` | the `Fin 3` tag (check 5) | proved |
| 2 | `windowRun_summary_of_halts` | the B6 instance: a halting space-bounded run is reported `halted` with its output's tag | proved |
| 2 | `FinTM.configBound_le_two_pow` | the four-factor clock bound (check 4) | proved |
| 3 | `clockCfg`, `wordPatch`, `Cfg.Stopped` | the step clock's layout | definitions |
| 3 | `exists_stepClockTMVia` | **H3-clock**: the step-clocked runner, any alphabet | sorry |
| 3 | `exists_stepClockTM` | C1's draft statement, verbatim, derived from the joint one | proved (modulo the joint one) |
| 4 | `exists_windowLoopTM` | **H3-loop**: the unclocked windowed round loop | sorry |
| 4 | `exists_windowRunnerTM` | **H3**: the loop under the step clock, clock word supplied | sorry |
| 4 | `exists_configWindowRunnerTM` | **H3 with a configuration-count clock**: what `space_hierarchy` cites | sorry |
| 5 | `inputCell`, `Cfg.inputSymbol_eq_inputCell` | H5's semantics: the virtual input cell | proved |
| 5 | `NativeAt` and three lemmas | **H5, native device** | proved |
| 5 | `inputCell_sub_eq_none_iff`, `inputCell_of_drop`, `pairEncode_pairEncode_length`, `_drop` | the ruler device's correctness facts, empty payload included | proved |
| 5 | `RulerAt`, `rulerHostCfg` | **H5, bounded-prefix ruler device**: presentation and host layout | definitions |
| 5 | `exists_rulerTestTM` | the restoring suffix-boundary test | sorry |
| 5 | `exists_rulerDeviceTM` | the device's call rows: read the virtual cell, move the virtual head | sorry |
| 5 | `exists_rulerHostTM` | the ruler host: any native-input machine on a suffix input | sorry |
| 6 | `exists_selfStartupTM` | `U₀`'s startup: input head at `1`, empty output, table captured | sorry |
| 6 | `exists_selfUniversal` | **`U₀`**, forward ledger `C_α · (s + 1)` | sorry |
| 7 | `Complexity.B6Draft.space_universal` | the proposed addend-free restatement, `C · s` | sorry |
| 7 | `Complexity.B6Draft.space_universal_gated_form` | the gated statement follows from it | proved (modulo the proposal) |

All names are `Turing.*` except §7. The draft uses the proposed final names. None collides with
the imported library (the draft elaborates). The binary-position device is **not** stated; §10
Q3 says why.

## 2. What each statement provides, and to whom

### 2.1 The bridges (§1, all proved)

- **The space clause of the coding step.** `exists_codeTM` (`TuringMachine/Encoding.lean:609`)
  is time-only. `exists_codeTM_spaceUsed` has the same witness, the relabelling along
  `Fintype.equivFinOfCardEq`, and adds `spaceUsed` equality **at every time**. The reason is
  `relabelState_visitedByTapeHead`: by `relabelState_runFrom_init`
  (`TuringMachine/StateRenaming.lean:116`), the relabelled run is the original run with
  renamed states, so every head trajectory is unchanged. Consumer: `space_hierarchy`'s
  contradiction step ("relabel `M'` to a coded machine `N`").
- **The all-times space bound.** `ComputesInTime.spaceUsed_le_of_halt` holds over any alphabet.
  `ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le` packages it, together with
  `ComputesInTime.of_spaceUsed_le` (`SpaceComplexity/ConfigCount.lean:357`), into exactly the
  two hypotheses of `one_work_tape_binary_spaceUsed` (`TuringMachine/Robustness/SingleTape.lean:2290`),
  with time function `n ↦ configBound M n (s n)`. Consumer: the contradiction step. The
  normal form then applies directly to the alleged decider.
- **Window containment.** `inWindow_of_spaceUsed_le`: total space `≤ s` by time `t` puts every
  configuration up to `t` in the radius-`s` window. It uses `abs_pos_lt_card_visited` (`:248`)
  and `mem_visited_of_ne_none` (`:263`). `Cfg.inWindow_init` covers the runner's starting
  record. Consumer: the contradiction step, and every user of H3.
- **`D`'s packaging.** `decidesInSpace_of_alphabetReduction` takes a rich machine that halts with
  `[x ∈ L]` on every Boolean input, plus an all-times, all-rich-inputs space bound. It returns
  `SPACE` membership at `c · (S n + 1)`. The time function is the supremum over
  `Fin n → Bool` of chosen halting times: noncomputable, and that is harmless (check 7). It calls
  `alphabet_reduction_spaceUsed` (`TuringMachine/Robustness/AlphabetReduction.lean:854`).
  Consumers: `space_hierarchy`'s `L_D ∈ SPACE g`, and later any rich-alphabet space decider
  (Savitch-style programs aside).
- **`CodeTM.one_le_spaceUsed`**: a coded run always visits at least one cell. This is the
  row-1 ledger's `s ≥ 1`, used by the addend-free `space_universal`.

### 2.2 H3: the windowed runner (§2 semantics, §3 clock, §4 machines)

**The semantics.** `windowRun M s upd N c τ` is a pure function. It runs `N` rounds; each round
tests for a halt, else steps if the successor is windowed, else reports `left`. The tag is
updated by `upd` with each step's emission. It is the specification behind all three machine
statements, and it is where the auditor's arithmetic lives:
- `windowRun_halted_of_run` is the forward direction B6 uses;
- `windowRun_spec` characterizes all three exits, for consumers that need the converse;
- `windowRun_tag` says the tag is the summary of the output, with nothing buffered (W1);
- `windowRun_stop_unique` says a stop does not depend on the clock;
- `windowRun_exhausted_of_live` and `windowRun_halts_on_last_transition` are the sanity pair:
  `N` rounds miss a halt on the `N`-th transition, and `t + 2` rounds catch a halt at `t + 1`
  together with its emitted bit.

**The tag.** It is generic: `T` with `upd` and `hupd : upd τ none = τ`, the record step's own
hypothesis (`TuringMachine/Build/CfgRecord.lean:4308`). The `Fin 3` instance is
`summaryTag`, with `outSummaryCode` (`empty ↦ 0`, `accept ↦ 1`, `dead ↦ 2`). Its compatibility
lemma `summaryTag_append` is proved from `outSummary_append_congr`
(`SpaceComplexity/ConfigGraph.lean:135`). `outSummaryCode_eq_one_iff` says tag `1` is exactly
the output `[true]`.

**The clock (§3, H3-clock).** `exists_stepClockTMVia` is the step-clocked runner over any
alphabet with a digit embedding: one countdown tick per physical body step, with exits `finish`
(the body stopped: halted, or in a designated stop state) and `timeout`. It follows C1's draft
and adds four things (§5):
- the alphabet generalization;
- distinctness of the exits;
- an exact counter-tape endpoint;
- a trajectory clause that bounds the host's space.

**The loop (§4, H3-loop).** `exists_windowLoopTM` is the round loop without a clock: test row,
then step row, back to the anchor, with the two stop states `stop halted` and `stop left`. Its
contract has three parts:
- for **every** `N`, the loop is where `N` rounds of `windowRun` say, at a time
  `≤ C · N · (L + |x| + 1)`;
- it never stops before the semantic run does;
- every head stays within `C · (L + 1)` of its start **at all times**.

Here `L = recordLength k |x| s` (`TuringMachine/Build/RecordTable.lean:150`).

**The runner (§4, H3).** `exists_windowRunnerTM` is the loop under the step clock, with the clock
word supplied by the consumer. All three outcomes are exposed:
- halt and window exit are **certified** whenever `C · N · (L + |x| + 1)` is within the clock;
- they are **determined** (the record of a stopping `windowRun` is on tape `0`, the clock
  interval holds a same-width word, and everything else is restored);
- clock exhaustion carries no tape claim.

It also states a time bound `5d + 2|w| + 3`, the envelope `C · (L + |w| + 1)`, an explicit
`spaceUsed` bound, and silence.

**The B6-facing runner (§4).** `exists_configWindowRunnerTM` builds its own clock. Its guarantee
is phrased by the **configuration count**: if `N ≤ configBound M |x| s + 1` rounds stop, the
runner reports their exit and record. The `+ 1` is the extra halt-test round of check 4. Space
is `O(L)` with constants depending only on `M` and `upd`. Restoration holds at `halted` and
`left`. Its statement is **clock-agnostic**: the docstring gives two fill routes.
- **Route A** is the step clock: one clock for B6 and C1.
- **Route B** is the round counter `counterLoopTMVia` (`TuringMachine/Build/CounterLoop.lean:614`),
  proved today. It merges halt and window exit into its one optional early exit (`_run_escape`,
  `:1306`), takes clock exhaustion as `done` (`_run_done`, `:1220`), and distinguishes the two
  escapes afterward by a test on the unchanged record. This is exactly the auditor's row 3.

Consumers:
- `space_hierarchy` (the runner at `U₀`);
- C1 (the clock only);
- later, any windowed simulation;
- S1b's re-derivation if it comes back (registry row H3, `machine-library-design.md:3060`).

### 2.3 H5: the input devices (§5)

**One interface: a presentation predicate plus a read and a move.** A device presents a
virtual input `y` at a virtual position `i` inside a host configuration over a physical input
`z`; `inputCell y i` is the virtual cell, with the input-tape convention
(`Cfg.inputSymbol_eq_inputCell`). There are two devices.
- **Native** (`NativeAt`): `z = y`, physical head = virtual head. Reading is the native read
  (`NativeAt.inputSymbol_eq`), and moving is the native clamped move (`NativeAt.move`). There is
  nothing to store. This is H2's seam clause and `U₀`'s device. `nativeAt_init` records that
  `Cfg.init` presents at position `1`, where `U₀`'s startup must leave the head (check 2).
- **Bounded-prefix ruler** (`RulerAt`, the gate's row 1): `z = header ++ y` with header length
  `ℓ > 0`, the physical head at `ℓ + i`, and a unary ruler `true^ℓ` on a work tape. Its
  correctness facts are proved, with the empty payload included:
  - `inputCell_sub_eq_none_iff`: the physical cell `p - ℓ` is blank exactly when `p = ℓ`;
  - `inputCell_of_drop`: away from `0`, the virtual cell is the physical cell `ℓ + i`;
  - `pairEncode_pairEncode_length` and `_drop`: `space_universal`'s input is a header of length
    `2|bits s| + 2|α| + 4` followed by `x`.

  There are three machine statements:
  - `exists_rulerTestTM`, the restoring boundary test: `C · (ℓ + 1)` steps, every head restored,
    ruler head within `ℓ + 1`;
  - `exists_rulerDeviceTM`, the call rows "read the virtual cell" and "move the virtual head",
    as asked;
  - `exists_rulerHostTM`, a lockstep transformer with pauses, the Z1 pattern of `vhostEmitTM`
    (`TuringMachine/Build/VirtualInput.lean:140`). It runs **any native-input machine**, in
    particular H2's block, on the suffix input. It uses `≤ C · (ℓ + 1)` host steps per source
    step, the same bank visits, and `ℓ + 2` ruler cells. This is the H2 note's O11: H2's input
    is native, so a suffix device must transform a native machine, not be called by it.

**Why both call rows and a host.** The brief asks for contracts that a step block can call. H2
as delivered reads its input natively (`h1RecordTM` and the selector read the input symbol in
their transitions, `TuringMachine/CodeSimulator.lean:2096`, `:3012`), so it cannot call a
device. The host makes the device usable with H2 unchanged, and the call rows are its
components and the interface for a future device-generic step block. §10 Q9 recommends gating
all three and filling the call rows inside the host's fill.

### 2.4 `U₀` (§6)

- `exists_selfStartupTM c`: from `R.initCfg (pairEncode α w)`, at a time `T` that depends on
  `α` only, and not earlier, the machine is at its exit with the following.
  - The input head is at `1` and the output is empty; it was empty at every earlier time.
  - Tape `1` holds `tableBitsK` of the decoded table.
  - Tape `2` holds the initial state in unary from cell `2`, which is H2's summary tape for an
    empty output.
  - Tape `0` is blank, and every head is at `0`.

  The space up to `T` is `≤ B_α`. This is precisely H2's seam relation (`h1RoundRep`,
  `TuringMachine/CodeSimulator.lean:4722`) for the decoded machine's initial configuration. It
  is stated with library notions only, so it does not depend on the H2 promotion's names.
- `exists_selfUniversal c`: the forward ledger. The machine coded by `α` halts on
  `pairEncode α w` with output `o` within `s` cells ⟹ `U₀` halts on the same input with output
  `o` within `C_α · (s + 1)` cells. Generic in the effective scheme; B6 uses
  `c := TimeHierarchy.code` (`TimeHierarchy/Diagonal.lean:107`). Only the forward direction is
  claimed, which is all the window route uses (gate note 6).
- **What it assumes of H2** (stated in the sketch). These are `h1Round_effect` as delivered
  (`:4780`) at `k = 1`, and the H2 draft's additive `roundTM_iterate`/`roundTM_visited`
  (`h2/StepBlockDraft.lean:800`, `:854`, proved from the contract):
  - each round is one source step, positive and at most `50 · (|table| + 1)` long;
  - it is silent and updates the summary cell by the emission;
  - the mirrored head is at its start or end, and the auxiliary heads stay within the bound and
    return home.

  The **emission** is forwarded by a host-side leaf: blank the summary cell before each round,
  apply the round to the source configuration *with its output erased* (Rep reads the output
  only through the cell), read the exact emission (`summaryEmit none b = b`), emit it, and blank
  the cell again. No block variant is needed, which agrees with the H2 note §2.3.

### 2.5 The addend-free `space_universal` (§7)

`Complexity.B6Draft.space_universal` is the proposed text: `C · s` in place of
`C · (s + logSpace |x| + 1)`, otherwise byte-identical. `space_universal_gated_form` derives
the gated statement from it in six lines, so the proposal only strengthens the theorem. Its
sketch is the gate's row-1 route: the header ruler, the ruler host around `U₀`'s round loop,
and the ledger `ℓ ≤ (2|α| + 6) · s` from `s ≥ 1`.

## 3. How `space_hierarchy`'s fill uses them

The restated sketch (`audits/evidence/b6-restatement/`, `Hierarchy.lean` after the patch,
lines 169–258), step by step.

1. **Inclusion**: unchanged (`SPACE.mono_const`).
2. **`U₀`**: `exists_selfUniversal TimeHierarchy.code`, named by `Classical.choose`, as
   `univTM` is (`TimeHierarchy/Diagonal.lean:110`).
3. **The diagonalizer `D`**, over `RecSym U₀.State (Fin 3)`, with these phases:
   - (i) validation by `inputFoldTM` (`TuringMachine/Build/Scan.lean:535`); a foreign symbol
     answers `false` in `O(1)` cells;
   - (ii) `bits (g n)` by `g`'s witness, lifted and captured. Its all-times bound is
     `ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le` (`O(g n)` cells);
   - (iii) the initial record of `U₀.tm.initCfg x` at radius `r = g n` with tag `0`
     (`outSummaryCode_nil`), by `exists_recordInitTM` (row 18, `RecordTable.lean:2970`, in
     flight);
   - (iv) `exists_configWindowRunnerTM U₀ summaryTag summaryTag_none` from that record
     (`Cfg.inWindow_init`);
   - (v) on exit `halted`, a test row (`exists_recordTestTM`, `CfgRecord.lean:4971`) for tag
     `= 1` answers `false` if it holds, `true` otherwise; on `left` or `exhausted`, answer `true`.

   `D` halts on every input, since the runner always exits. Its space is that of (ii), plus the
   record and `C · (L + 1)`, all `O(g n)` uniformly in the code part, because
   `L = recordLength k₀ n r` and `posWidth n ≤ logSpace n + 1 ≤ 2 g n`. All times are covered:
   the runner's envelope holds up to its exit.
4. **Packaging**: `decidesInSpace_of_alphabetReduction` at `S n := C_D · g n` gives
   `L_D ∈ SPACE g`.
5. **Contradiction.** Take a decider `M` of `L_D` within `c₀ · f`.
   - `computesFunInTime_and_forall_spaceUsed_le` gives the normal form's hypotheses;
     `one_work_tape_binary_spaceUsed` gives `M'`, and `exists_codeTM_spaceUsed` gives `N`,
     with `α_M := code.encode N`.
   - On `x = pairEncode α_M 1^{N₀}`, `exists_selfUniversal` gives `U₀`'s halting run with output
     `[x ∈ L_D]` within `r` cells, by the gate's arithmetic `C_α(c(c₀ f n + 1) + 1) ≤ A f n ≤ g n`.
   - By `ComputesInTime.of_spaceUsed_le` it halts by `configBound U₀ n r`, and its space bound
     holds at that time (`spaceUsed_le_of_halt`).
   - `windowRun_summary_of_halts` at `N := configBound + 1` gives exit `halted` with tag
     `outSummaryCode (outSummary [x ∈ L_D])`, and the runner's certification clause makes `D`
     see exactly that. By `outSummaryCode_eq_one_iff`, `D` answers `false` iff `x ∈ L_D`: the
     contradiction.

**Still to be written in the fill (not hosts):** the radius phase, which S1b's private
`s1b_normalize_radius` and `s1b_constructor_time` (`SpaceComplexity/ConfigGraph.lean:746`, `:769`)
already do for its own radius and are promotion candidates; `D`'s phase composition; and the
contradiction arithmetic. The "clock-width phase" of the restated sketch is gone, because the
runner builds its own clock.

## 4. An addend-free `space_universal`, and when to strengthen

**How.** The startup scans the header, writing one ruler cell per header cell. The ruler
length `ℓ = 2|bits s| + 2|α| + 4` is the header's (`pairEncode_pairEncode_length`, `_drop`),
and the head is left at `ℓ + 1`, virtual position `1`. Then canonize `α` as in
`exists_selfStartupTM`, and run `U₀`'s round loop through `exists_rulerHostTM`. The ledger:
- the startup is `B_α`;
- the ruler is `ℓ + 2`;
- the rounds are `s + O_α(1)`;
- `s ≥ 1` (`CodeTM.one_le_spaceUsed`) and `|bits s| ≤ s` (`Turing.length_bits_le_self`,
  `Encoding.lean:269`) give `ℓ ≤ (2|α| + 6) · s`.

So the total is `≤ C_α · s`.

**When: recommendation, strengthen at the H5 statement gate, as part of its pack** (not now as
a separate gate, and not after H5's fill). The reasons:
- **The stronger sketch must cite H5's ruler host.** Gating the statement before the host's
  contract has passed its own gate would gate a sketch on an ungated host, which is what the
  host-first rule forbids.
- **No consumer depends on `space_universal`** (gate note 6), so nothing waits on the timing.
- **One pack covers it.** H5's gate already examines the ruler device. Adding the one-statement
  change of `Hierarchy.lean` (the `C · s` text in §7, its revised sketch, and the derivation
  `space_universal_gated_form` as evidence that it only strengthens) costs one extra row, not
  one extra gate.
- **It removes the declared deviation.** The deviation "`+ logSpace |x| + 1` … presumes the
  standing convention" goes, and the statement becomes the book's `C · t`.

The alternative is to keep the gated statement and record the stronger form as an implementation
choice, which the auditor allowed. It is weaker than the book with no consumer-side reason, so
it is not recommended.

## 5. The joint clock with C1: what C1 cites

**C1 cites `Turing.exists_stepClockTMVia`**, at `Γ := Bool` and `e := Function.Embedding.refl Bool`,
or its `Bool` corollary **`Turing.exists_stepClockTM`**. The corollary is C1's draft statement
(`c1/C1HostsDraft.lean:376`) **word for word**. It is proved in `B6Hosts.lean` from the joint
statement, so C1's design and draft proofs are unaffected. C1's `clockCfg`
(`c1/C1HostsDraft.lean:363`) is the `Bool` instance of the joint `Turing.clockCfg`, with the same
field layout.

What the joint statement adds to C1's draft, and why:

| Addition | Why |
|---|---|
| any alphabet `Γ` with a digit embedding `e`, the counter digits embedded, as in `counterLoopTMVia` | H3 runs over the record alphabet |
| `finish`, `timeout` injective and distinct; `inj` distinct from both | so a consumer can dispatch on exits; the runner maps `finish (stop e)` to its exits |
| the counter tape's endpoint is the start patched with a same-width digit word (`wordPatch`), not an arbitrary `ct'` | restoration outside the counter's cells, which H3's endpoint states |
| a trajectory clause: up to the exit, the body heads equal the body's own heads at some body time `≤ τ` (or `≤ d`), and the counter head stays in `[cp - 1, cp + |w|]` | H3's space and envelope; without it a clocked host's space is unbounded by the contract |

The constants `5τ + 2|w| + 2` and `5d + 2|w| + 2` are C1's. I checked them against the
amortized ledger.
- **Finish.** `τ` decrements cost at most `4τ + 2|w|` (`counterOverhead_le_of_le`,
  `CounterLoop.lean:511`). With `τ` body steps and one stop dispatch that is `5τ + 2|w| + 1`.
- **Timeout.** `d + 1` decrements including the underflow cost at most `4d + 2|w| + 2`
  (`counterOverhead_le`, `:541`). With `d` body steps that is `5d + 2|w| + 2`.

Both hold if the stop check is fused into the first decrement step and a halting body transition
lands directly on `finish none`. This is an INFERRED plan, not a proof. If the fill needs a
dispatch step more, the statement gate should allow `+ 3`.

Shared sequencing: one statement phase covers the clock for B6 and C1, the "H3-clock" row of C1's
plan (`c1/C1-design.md` §5). B6's critical path does **not** wait for the clock's fill: B6
cites the clock-agnostic `exists_configWindowRunnerTM`, whose Route B uses the proved
`counterLoopTMVia` (§10 Q1).

## 6. Dependencies

| Dependency | Needed by | Status | Note |
|---|---|---|---|
| **H2 promotion** (F7-1(a), `backlog.md:553`; the H2 draft, `h2/H2-design.md`) | `exists_selfUniversal` (its fill); `exists_rulerHostTM` is generic and does not need it | private and proved as `h1Round_effect`; the H2-S statement gate pending | `U₀` is stated against the delivered contract. Its statement mentions no H2 name, so a renaming at promotion changes only the sketch. Assumed: §2.4. |
| **Record-table rows 17–18** (`exists_recordTemplateTM`, `exists_recordInitTM`, `RecordTable.lean:2914`, `:2970`) | `space_hierarchy`'s fill (the initial record); not the hosts | in flight, sorried (row 17's bound-field prefix is proved privately, `rt_exists_boundTM`, `:2696`) | `backlog.md:614`: "rows 17–18 continue for B6's window route" |
| `exists_recordStepTM`, `exists_recordTestTM` (`CfgRecord.lean:4308`, `:4971`) | H3-loop | **proved** | |
| `counterLoopTMVia` and its contracts | Route B of H3, and the step clock's proof | **proved** | |
| **MIG-0a / MIG-0b** (design §16a) | the phrasing, later | MIG-0a gate round 2 pending; MIG-0b not designed | Stated in the existing style. H3-loop is a MIG-0b round-layer instance (a return-or-escape round iterated), and the step clock is a round with a joint-trajectory clause. Re-phrase as `Contract`s when MIG-0b lands, by adapter, as the H2 note §3.3 proposes. Do not wait. |
| C1's step clock | Route A of H3 | joint statement here | §5 |
| `OutSummary` | the `Fin 3` tag | public in `ConfigGraph.lean:104` | its home matters for layering (§8, Q4) |
| `alphabet_reduction_spaceUsed`, `one_work_tape_binary_spaceUsed`, `of_spaceUsed_le` | the bridges | **proved** | |
| `universalCanonTM`, `universalCaptureTM`, `universalCanon_complete` (`TuringMachine/UniversalStartup.lean:238`, `:405`, `:287`), `FinTM.timed_rewind` (`TuringMachine/Simulation.lean:446`) | `U₀`'s startup | **proved** | |

## 7. The auditor's checks and sanity obligations, mapped

| Gate requirement (`b6-restatement-findings.md`) | Where it is met |
|---|---|
| Row 1: a bounded-prefix device with a unary ruler; addend-free `C · s` | `RulerAt`, `exists_rulerTestTM`, `exists_rulerDeviceTM`, `exists_rulerHostTM`; `B6Draft.space_universal`; the ledger facts `pairEncode_pairEncode_length`/`_drop`, `CodeTM.one_le_spaceUsed` |
| Row 3: one optional early exit plus clock exhaustion; merge halt and window exit, then distinguish | Route B of `exists_configWindowRunnerTM`'s sketch; the contract itself exposes all three outcomes |
| Note 7: carry the invariants into H3's contract | the clock surplus (`N ≤ configBound + 1`); the halt test (`windowRun`); scratch and heads restored (endpoints); containment (`inWindow_of_spaceUsed_le`) |
| Note 8: spell out startup, head reset, output and all-times as contracts | `exists_selfStartupTM` (startup, reset, empty output); `ComputesInTime.spaceUsed_le_of_halt` (all times) |
| Check 1, inclusion | unchanged, outside this draft |
| Check 2, startup at input position `1`, empty output, table on a work tape, fresh simulated cells; H2 restores administrative heads | `exists_selfStartupTM`'s endpoint and output clause; `nativeAt_init`; `U₀`'s sketch cites H2's "home" clause |
| Check 3, uniform space: validation, `bits (g n)`, record rows restore, `posWidth ≤ 2 g n` | §3 step 3; H3's envelope is `C · (L + 1)` with `C` depending only on `M`, `upd`; the record rows' restoration is in the loop's endpoint |
| Check 4, clock bound, strict surplus and the extra halt-test round | `FinTM.configBound_le_two_pow` (proved); `windowRun_exhausted_of_live` (the surplus is needed); `N ≤ configBound + 1` in `exists_configWindowRunnerTM` |
| Check 5, the `Fin 3` tag, `accept` = exactly `[true]`, every exit yields a bit, totality | `summaryTag`, `summaryTag_append`, `outSummaryCode_eq_one_iff`; the runner always exits (time bound); `D` answers on all three exits |
| Check 6, normal form, all-times bridge, relabelling, containment, the flip | `computesFunInTime_and_forall_spaceUsed_le`, `exists_codeTM_spaceUsed`, `inWindow_of_spaceUsed_le`, `windowRun_summary_of_halts` |
| Check 7, alphabet reduction: all rich inputs, finite maxima of halting times | `decidesInSpace_of_alphabetReduction` (proved, by exactly that construction) |
| **Sanity: a restoring suffix-boundary test, empty input included** | `exists_rulerTestTM` (its input is arbitrary); semantic content proved as `inputCell_sub_eq_none_iff` for every `z` |
| **Sanity: `U₀` startup with empty output and input position `1`** | `exists_selfStartupTM` (`inputPos = 1`, `output = []` at every time up to the exit) |
| **Sanity: all-time space preservation under state relabelling** | `MultiTapeTM.relabelState_spaceUsed` (∀ `t`, proved) |
| **Sanity: an H3 run halting on its final simulated transition while emitting the deciding bit** | `windowRun_halts_on_last_transition` (proved), with `windowRun_exhausted_of_live` as its negative twin; the machine contracts reduce to `windowRun` |
| Row 4 (Finding B wording) and row 2 (stale §12.8a row, `machine-library-design.md:1935`) | records, not statements: the design-record update should mark line 1935 superseded and point to H3/H5 here |

## 8. Proposed homes

| Declarations | Home | Reason |
|---|---|---|
| `relabelState_visitedByTapeHead`, `_spaceUsed` | `TuringMachine/StateRenaming.lean` | next to `relabelState_runFrom_init` |
| `exists_codeTM_spaceUsed`, `CodeTM.one_le_spaceUsed` | `TuringMachine/Encoding.lean` | next to `exists_codeTM` |
| `ComputesInTime.spaceUsed_le_of_halt`, `computesFunInTime_and_forall_spaceUsed_le`, `inWindow_of_spaceUsed_le`, `decidesInSpace_of_alphabetReduction` | `SpaceComplexity/ConfigCount.lean` | next to `of_spaceUsed_le`. Its closure already contains `alphabet_reduction_spaceUsed` (Basic → Encoding → SingleTape) |
| `Cfg.inWindow_init` | `TuringMachine/Build/CfgRecord.lean` | next to `Cfg.InWindow` |
| `WindowExit`, `windowRun` and lemmas, `exists_windowLoopTM`, `exists_windowRunnerTM`, `exists_configWindowRunnerTM`, `FinTM.configBound_le_two_pow` | new **`TuringMachine/Build/WindowRun.lean`** (host H3) | imports `Build/CfgRecord`, `Build/StepClock`, `SpaceComplexity/ConfigCount` (for `configBound`). That a Build file imports a SpaceComplexity file is a layering question (Q5) |
| `outSummaryCode`, `summaryWord`, `summaryTag` and lemmas, `windowRun_summary_of_halts` | `SpaceComplexity/ConfigGraph.lean`, next to `outSummary`, replacing S1b's private copies (Q4) | the tag instance belongs with the summary |
| `clockCfg`, `wordPatch`, `Cfg.Stopped`, `exists_stepClockTMVia`, `exists_stepClockTM` | new **`TuringMachine/Build/StepClock.lean`** (H3-clock, shared with C1) | imports `Build/CounterLoop`, `SymbolLift` |
| `inputCell`, `NativeAt`, `RulerAt`, `rulerHostCfg` and lemmas, the three ruler rows | new **`TuringMachine/Build/InputDevice.lean`** (H5) | next to `Build/VirtualInput.lean` (Z1); imports `Build/Embed`, `Encoding` |
| `exists_selfStartupTM`, `exists_selfUniversal` | new **`TuringMachine/SelfUniversal.lean`** | imports `UniversalStartup`, the H2 module (`Build/StepBlock.lean` after the promotion) |
| the `C · s` statement | `SpaceComplexity/Hierarchy.lean`, replacing `space_universal`'s statement at the H5 gate (§4) | |

## 9. Size estimates (ESTIMATE unless marked)

| Item | Lines landed | Basis |
|---|---|---|
| This draft's proved part (bridges, semantics, tag, device facts) | about 330 proof lines, 600 with docstrings (MEASURED in the draft) | lands with the statements |
| H3-clock `exists_stepClockTMVia` (joint with C1) | 700–1,400 | C1's estimate (`c1/C1-design.md` §5); the round induction of `counterLoopTMVia_run_done` is the template |
| H3-loop `exists_windowLoopTM` | 500–900 | one phase host over two proved rows; `exists_recordTestTM`'s own proof is about 285 lines (MEASURED, `CfgRecord.lean:4971–5256`) |
| H3 `exists_windowRunnerTM` | 250–500 | an instantiation of the clock plus one dispatch |
| `exists_configWindowRunnerTM` | 500–900 (Route A) or 700–1,200 (Route B, a second body over `counterLoopTMVia`) | the clock-writing phase plus the ledger |
| `exists_rulerTestTM` | 150–300 | two lockstep sweeps |
| `exists_rulerDeviceTM` | 250–450 | the test plus three moves, seamed |
| `exists_rulerHostTM` | 400–800 | `VirtualInput.lean` is 508 lines for the Z1 pair (MEASURED) |
| `exists_selfStartupTM` | 500–1,000 | `UniversalStartup.lean` is 591 lines (MEASURED) and is mostly reused |
| `exists_selfUniversal` | 700–1,300 | the iterate lemma, the output leaf, the halt redirect, the space ledger |
| `space_hierarchy`'s fill (`D`, the contradiction, the packaging) | 1,500–3,000 | |
| the addend-free `space_universal`'s fill | 800–1,500 | the ruler writer, a startup variant, the host composition |

**Total for B6 on this route: about 6k–12k lines**, of which about 0.6k is in this draft and about
1–1.4k (the clock) is shared with C1.

## 10. Open questions, each with a recommendation

- **Q1. Which clock does B6's runner use in its fill?** Route A, the step clock, gives one
  clock for B6 and C1. Route B, `counterLoopTMVia`, is proved today and gives a clean exhaustion
  endpoint. *Recommendation:* state H3 as drafted, with `exists_configWindowRunnerTM`
  clock-agnostic, so the choice is the fill's. Fill by **Route A if the joint clock is filled
  first** (C1's plan puts it early), and otherwise by Route B, so that B6 does not wait.
  `exists_windowRunnerTM` is the step-clocked composition either way; C1 and future consumers
  use it.
- **Q2. Strengthen `space_universal` to `C · s` now, or at H5's gate?** *Recommendation:* at
  H5's statement gate, in the same pack (§4).
- **Q3. The binary-position device.** It costs `O(log |x|)` and serves only the gated
  `space_universal`'s logarithmic addend. The ruler device does better on the same input layout,
  and `exists_recordStepTM` already carries its own binary input seek (`exists_inputSeekTM`,
  `TuringMachine/Build/InputCall.lean:294`). *Recommendation:* **do not state it for B6.** Keep
  the registry row (design §14, line 3062) for other consumers, under the rule of admission.
- **Q4. The three summary encodings and S1b's private copies.** `outSummaryCode` and
  `summaryTag` duplicate, value for value, the private `sumCode` (`ConfigGraph.lean:393`) and
  `s1b_summaryWord`, `s1b_tagUpdate`, `_none` and `_output` (`:629–660`). The H2 note's O4 adds
  a third code, `outputSummary : List Bool → Option Bool` (`CodeSimulator.lean:1959`).
  **This is disclosed duplication** (policy §1, *Duplication*). *Recommendation:* land the
  public versions in `ConfigGraph.lean` and re-point S1b's privates at them in the same PR,
  which leaves no copy. The dedup of the third encoding goes with H2's O4 item, as a
  maintainer-owned dedup item.
- **Q5. Layering: `Build/WindowRun.lean` imports `SpaceComplexity/ConfigCount.lean`** for
  `configBound`. There is no cycle, since the new module is imported by nobody in that closure.
  *Recommendation:* accept it. The alternative, moving `configBound` down into Build, is a
  shared-file move with a wide replay and is not worth it now. If the gate prefers, split
  `exists_configWindowRunnerTM` and `configBound_le_two_pow` into
  `SpaceComplexity/WindowClock.lean`, and keep `Build/WindowRun.lean` free of SpaceComplexity.
- **Q6. Existentials or named machines.** The contracts are `∃`-modules in the house style of
  `exists_recordStepTM`. MIG-1 asks for named witnesses in new work. *Recommendation:* gate them
  as `∃` statements, which is what a statement gate can check without a construction. Name the
  witnesses at fill time (`def windowRunnerTM …` with the `∃` statement as its corollary), as the
  H2 promotion does. `U₀` is named by `Classical.choose`, as `univTM` is.
- **Q7. `Contract` phrasing (MIG-0b).** *Recommendation:* existing style now, and adapters when
  the round, segment and joint-trajectory layers land. The loop's every-`N` clause and the clock's
  trajectory clause are exactly what those layers will carry.
- **Q8. `U₀` generic in the scheme.** *Recommendation:* keep it generic. U-1 and EXPCOM-style
  users may want another scheme, and nothing in the proof uses the particular `code`.
- **Q9. Do the ruler call rows need their own gate row?** Their consumers are the ruler host
  (internal) and a future device-generic step block (none yet). *Recommendation:* gate all
  three statements together; `exists_rulerTestTM` carries the auditor's sanity obligation.
  Fill the call rows inside the host's fill, and drop them only if no second consumer appears
  by MIG-0b.
- **Q10. Time.** No B6 statement needs `U₀`'s time or a polynomial time for `D`. The record step
  costs `O(L + |x|)` per round because of its native input seek (`CfgRecord.lean:4308`). The
  runner's time is exponential in `L`. *Recommendation:* no time clause on `U₀` now. U-1 may add
  one under its own gate.
- **Q11. `windowRun` is noncomputable** (classical tests of halting and window membership).
  *Recommendation:* fine for a specification; the machines realize it. No consumer computes it.

## Evidence produced for this note

- `b6hosts/B6Hosts.lean` (sha256 in `elaboration.log`).
- `b6hosts/elaboration.log`: the read-only elaboration (0 errors, 10 sorry warnings), and the
  axiom probe of a scratch copy (`b6hosts/work/AxProbe.lean`) with `#print axioms` appended for
  all 55 declarations.
- `b6hosts/work/`: the incremental probes `T0`–`T7`, kept for the record; none is a deliverable.
