# H2: promoting the step block. Design note for the statement gate

Maintainer draft, 2026-10-13. It concerns host H2 of `machine-library-design.md` §14 (row at
line 3059) and backlog F7-1(a) (`backlog.md:553–557`). It was written read-only against the
campaign tip checkout `wt-h2`. Every `file:line` below refers to that checkout unless it names
`h2/`, which means this directory.

**Ready for the user: the statement-gate pack for the H2 promotion can be assembled from this
note, `h2/StepBlockDraft.lean`, `h2/elaboration.log`, `h2/fidelity.log` and the C1 probe.**

**Recommendation in one line: promote as is now.** The public statement is the delivered
contract, renamed, phrased in the existing style. The proofs move unchanged, and generalization
is deferred to the consumers' own designs.

Contents:
1. What the delivered contract states, and what it does not
2. What each named consumer needs, with a verdict
3. Recommendation: promote as is, or generalize at promotion; `Contract` phrasing and migration
4. The proposed public module, the `CodeSimulator.lean` changes, the replay closure, the gates
5. Open questions, each with a recommendation
6. Size estimate (ESTIMATE)
7. Evidence produced for this note

Appendix A gives the complete rename map, Appendix B the verification commands.

---

## 1. The delivered contract

### 1.1 Setting

The private host lives in `TCSlib/Complexity/TuringMachine/CodeSimulator.lean`, in namespace
`Turing.MachineFormat`. None of its declarations uses the section variable `F`. It is one
finite machine per work-tape count `k`:

* **`h1RoundTM k : MultiTapeTM (k + 2) Bool (Σ key, h1RoundPh k key)`** (`:3979`). This is
  `phaseHostTM` over a 15-key schedule (`h1RoundKey`, `:3919`; `h1RoundPart`, `:3939`;
  `h1RoundRed`, `:3959`). The schedule runs as follows:
  - lookup, by the selector `h1SeekTM` (`:3012`), itself a phase host over a router and the
    whole-record skipper;
  - clear the old state word, using catalog `skipTM`, `skipBackTM` and `clearTM`;
  - read and execute the record's fixed fields (`h1RecordTM`, `:2096`);
  - install the successor (`h1SuccTM`, `:2454`);
  - restore both auxiliary heads.

  Its control types depend only on `k` (`h1RoundPh_finite`, `:3983`).
* **The tapes.** Work tapes `0..k-1` mirror the simulated machine's work tapes. Tape `k`
  (`h1TableTape`) holds the table word. Tape `k + 1` (`h1SummaryTape`) holds the output summary
  at cell 0, a blank at cell 1, and the current state in unary from cell 2 on (`h1SummaryState`,
  `:3763`).
* **The exits** (`h1RoundExit`, `:3954`). These are `⟨.entry, ()⟩`, which is also the start
  state, and `⟨.halt, ()⟩`. Both are live states, and `.halt` is stationary.

### 1.2 `h1Round_effect` (`:4780`) in mathematical English

Fix a transition table `tr` of a `k`-work-tape binary machine with `n + 1` states. Fix an input
`x`, a live source configuration `c` on `x` in state `q`, and let `a = tr(q, input read of c,
work reads of c)` be the action the source takes. Let `d` be a configuration of the step block
on the **same input `x`**. Assume that `d` is at `entry` and **represents** `c`
(`h1RoundRep`, `:4722`), which means:
* the native input head of `d` is at `c`'s input position;
* the first `k` tapes and heads of `d` are `c`'s;
* tape `k` holds `tableBitsK tr` as a buffer word;
* tape `k + 1` holds `summaryCells(outputSummary(c.output), unary(q))`;
* both auxiliary heads are at cell 0.

The control state and the physical output of `d` are unconstrained.

Then there is a time `T` with `0 < T ≤ 50·(|tableBitsK tr| + 1)` such that the configuration
`e` reached at time `T` satisfies the following.

1. **Endpoint.** `e` is at `entry` if `a` has a successor and at `halt` otherwise, and `e`
   represents `a.apply c`, the source's next configuration (with an empty state word if `a`
   halts). Its summary cell is `summaryEmit(old summary, a.output)`.
2. **Cut.** Strictly between 0 and `T`, the block is live and is at neither `entry` nor
   `halt`.
3. **Silence.** The physical output equals `d.output` at every time up to `T`.
4. **Head envelope**, at every time `u ≤ T`:
   * the input head is at its start or its end position, within one cell of its start;
   * each mirrored head is at its start or its end position, within one cell of its start;
   * each auxiliary head is within `50·(|tableBitsK tr| + 1)` cells of its start.
5. **Home.** Both auxiliary heads are at cell 0 at time 0 and at time `T`.

The bound does not depend on `k`, `n`, `x`, the tape contents or the simulated time.

The endpoint is therefore fully determined:
* `Rep` fixes every tape and every head;
* the exit fixes the control;
* silence fixes the output.

Only `T` is existential. By the cut it is unique: it is the first positive time at `entry` or
`halt`.

### 1.3 The other promotion candidates

* **Whole-record skipper** (`h1SkipTM`, `:2687`).
  - `h1Skip_run` (`:2806`): from the reader's initial state, with a record of the action `a`
    under the table head, the skipper reaches its live exit `done (a.state.isSome)` after exactly
    `|actionBitsK a| + 1` steps. Only the table head changes, and it advances by the record's
    length.
  - `h1Skip_spec` (`:2921`): no exit is reached earlier, and at every time up to then the input
    position, all tape contents and the output are unchanged, and the table head's displacement
    is given exactly.
* **Successor-field leaf** (`h1SuccTM`).
  - `h1Succ_run` (`:2616`) gives the endpoint;
  - `h1Succ_cut` (`:2628`) gives the cut;
  - `h1Succ_heads` (`:2644`) gives the exact head trace.
* **Fixed-field reader** (`h1Record_effect`, `:2341`): an exact `4k + 5` steps, a framed effect
  and an envelope.
* **Run head bound** (`h1Run_headBound`, `:3638`): after `t` steps of any machine, every work
  head is within `t` cells of its start.

### 1.4 What the contract does not state

| Missing clause | Status |
|---|---|
| **Space** | No `spaceUsed` clause. It is *derivable* from the envelope: a mirrored head visits only the source's cells before and after the step, and an auxiliary head visits only `[-B, B]`. This is proved in the draft from the contract as the additive `roundTM_visited` and, over runs, `roundTM_iterate`. |
| **Input device** | **Native only.** The block's input *is* the simulated input (`d.inputPos = c.inputPos`, with both on the same `x`). Suffix or virtual inputs must come from a device that transforms a native-input machine in lockstep, as Z1's `vhostEmitTM` does (`Build/VirtualInput.lean:140`). That is not a step-block clause. |
| **Choice bit** | **None.** The table is deterministic. Section 2.4 shows that none is needed for C1. |
| **Output** | **Summary, not emission.** The block is silent. The emission updates a three-valued cell, which is empty, exactly `[true]`, or other (`outputSummary`, `:1959`; `summaryEmit`, `:1965`). The draft observes that `summaryEmit none b = b` (`summaryEmit_none`, proved). So a host that blanks the cell before each round finds that round's exact emission there afterwards, and can forward it or buffer it with the block unchanged. |
| **Exact time** | Only `0 < T ≤ 50·(|table| + 1)`. The proof computes more. In `h1Round_canonical` (`:4643`), `T = L + 3q + |record| + |tail| + |table| + |word| + 38`, and the lookup takes `L ≤ 5·|table| + 4` (`h1Round_lookup`, `:4596`, with the bound at `:4602`). The stated 50 is a convenient over-approximation. |
| **Composition over rounds** | Not stated. It is provided by the hosts (`counterLoopTM`) or by the additive `roundTM_iterate`. |
| **Halting** | The block never halts physically. `halt` is a live, stationary exit, and the consumer redirects it. |
| **Validation** | None. The table must be exactly `tableBitsK tr`, a canonized table. |
| **`Contract` form** | Not stated in that form, because MIG-0a's structure is not landed. See §3.3. |

---

## 2. The named consumers

Section 14 of the design names five consumers (H1, U-1, B6's universal machine, C1, EXPCOM).
The verdicts use three grades:
* **as is**: the delivered contract suffices;
* **small generalization**: an additive lemma, or a sharper clause whose proof already exists in
  the proof's components;
* **separate host**: the need belongs to another host.

### 2.1 H1, `MachineFormat.exists_uniformSimulator` (`:4938`)

**Needs.** One round under §12.7's `counterLoopTM` over `bits t` and Z1's `vhostEmitTM`:
* positive first return to the anchor, and a live escape (the simulated halt);
* a cut against both;
* silence, and a per-round bound independent of `t` and `x`;
* the summary verdict through the inherited `summaryClock_accepts` (`:2028`).

`counterLoopTM_run_done` (`Build/CounterLoop.lean:1383`) takes the round length as a *function*
`τ` of the body configuration. It also wants, for `0 < u < τ`, a state `s ≠ a` with
`exit ≠ some s`. That is exactly the cut, with `a = entry` and `exit = some halt`.

**Verdict: as is.** The block was designed for this consumer, and the H1 frontier
(`audits/b5a-fill-agent-reports/h1-2-REPORT.md`, items 1–4) needs no new block clause.

The assembly picks `τ` from the existential by choice. An optional `roundTime` function (§5,
O7) would spare it that.

### 2.2 EXPCOM

EXPCOM consumes **H1 only**. `exists_uniformMachineCode` is built from
`oneTapeMachineFormat.exists_polyCanonizer` and `.exists_uniformSimulator`
(`Diagonalization/EXPCOM.lean:154–156`). It never sees the step block.

**Verdict: as is, through H1 at `k = 1`.** It needs nothing beyond H1's assembly.

### 2.3 B6's `U₀`, and its sibling `space_universal`'s `SU` (RD-3)

The window route (`machine-library-design.md:3785–3810`; the sketch in
`audits/evidence/b6-restatement/hierarchy.patch:281–300`) runs one fixed self-applying `U₀`.
It uses one coded work tape, its own input head as the simulated one (H5's native device), and
"the H2 step block on the canonical table". It needs a forward ledger: `U₀` halts with the same
output, having visited at most `C_α·(s + 1)` cells.

| Need | Verdict |
|---|---|
| `k = 1` and the one-tape code table | **as is.** `TimeHierarchy.code` is the one-tape scheme. By `oneTapeMachineFormat.serialize_eq` its serialization is `serializeK`, whose table is `tableBitsK`. |
| Native input device | **as is.** Under self-application, `U₀`'s input is the simulated input. This is exactly `Rep`'s input clause. |
| The same output, verbatim | **as is, with a host-side leaf.** Blank the summary cell before each round. After the round, forward the cell (`summaryEmit_none` together with the summary clause), then blank it again. This is an `O(1)`-step leaf on tape `k + 1`, within the auxiliary envelope. No block variant is needed. |
| Space ledger `C_α·(s + 1)` | **small generalization (additive, proved in the draft).** By `roundTM_iterate`, the mirrored tape visits only cells that the source visits, and the auxiliary tapes stay in `[-B, B]` with `B` a constant of the table. The startup (canonizer) is a per-code constant. |
| An unclocked run until halt | **small generalization (additive).** `roundTM_iterate` gives every live prefix and "never at `halt` early". The final, halting round is `roundTM_effect` once more. A one-key phase redirect sends `halt` to a physical halting state. |
| `SU` only: the suffix input `⟨bits s, ⟨α, x⟩⟩` read through a binary position | **separate host (H5).** It must be a lockstep transformer of a native-input machine, like Z1, so that `Rep`'s native input clause transports (O11). |

### 2.4 C1, the NTIME hierarchy (`Diagonalization/NTimeHierarchy.lean`, `TuringMachine/NDCodes.lean`)

**Needs.** `exists_timed_universal_NDTM` (`NTimeHierarchy.lean:121`) maintains "both simulated
tapes on two dedicated real tapes, holds the canonized table on a third", and "passes its own
choice bits through" (`:103`). It runs at linear overhead `C·(t + 1)`, with a fused,
amortized countdown and the input read in place. `exists_ndAcceptsWithin_decider` (`:146`)
replays the same core with choices read from a counter tape. The §14 registry says "C1 (with a
choice-bit-indexed table)".

**Finding: no choice-bit generalization of the block is needed.** The probe
`h2/probe/C1LiftProbe.lean` proves `ndTable_eq_tableBitsK`, with 0 errors and 0 warnings. It
states that the table part of `CodeNDTM.serialize` (`NDCodes.lean:116`; choice bit outermost,
then states, then reads) is, bit for bit, `tableBitsK` of the **choice-lifted deterministic
table** on `2·(n + 1)` states:
* lifted state `p < n + 1` runs the `false` table at `p`;
* lifted state `n + 1 + q` runs the `true` table at `q`;
* every successor stays in the lower half.

A successor's bits depend only on its value (`actionBitsK_mapState_castLE`). So the unchanged
block, started from the lifted state `b·(n + 1) + q`, performs one nondeterministic step under
choice `b`.

| Need | Verdict |
|---|---|
| `k = 2` (`CodeNDTM` has two work tapes, `NDCodes.lean:97`) | **as is** |
| The choice-indexed table | **as is**, by `ndTable_eq_tableBitsK`, a pure lemma (about 40 lines) |
| Install the choice before each round | **host-side.** A small phase adds `b·(n + 1)` to the unary state word on tape `k + 1`, using a unary copy of `n + 1` made once at startup. Its cost per round is `O(n) ≤ O(|table|)`, a constant per code. In the deterministic replay `BF`, the bit comes from the counter tape. |
| A nondeterministic host: a guess step plus deterministic phases, and a nondeterministic counter loop | **separate host.** SC-3, the nondeterministic lifting that the C1 cluster already waits on (`AroraBarakChapters3-4Plan.md:844`) |
| In-place input (`UniversalStartup`'s virtual input) | **separate host (H5)**, as in §2.3 |
| The linear ledger `C·(t + 1)` | **as is**: per round `≤ 50·(|table| + 1)`, a per-code constant |

### 2.5 U-1, re-deriving the chapter-1 universal machine (`backlog.md:424–455`, merged with MIG-2)

**Needs** (`backlog.md:439–451`):
* full output (`universal`), and `true :: output` or `[false]` (`timed_universal`);
* per-code linear time with no `|x|` term;
* no deadline for `universal`, and divergence preserved (the converse);
* the frozen statements unchanged.

| Need | Verdict |
|---|---|
| Output: `universal` emits verbatim; `timed_universal` buffers, then emits `true :: buffer`, or emits `[false]` | **as is, host-side.** The forward-and-reset leaf of §2.3 sends each emission either to the output or to a buffer tape. |
| Per-code linear, with no `|x|` and no `t` in the round | **as is, qualitatively** |
| The converse (divergence preserved) | **small generalization (additive)**: `roundTM_iterate`'s "never at `halt` before the source halts" |
| In-place suffix input with `O(1)` cost per move (`universalInput_read`/`_move`, `UniversalStartup.lean:338, 373`) | **separate host (H5)**, wrapped as a lockstep device |
| **The frozen constant** | **does not fit as stated.** See below. |

The frozen constant: `timed_universal_concrete` (`Universal.lean:2844`) displays
`universalBlockBound c α = 3·|serialize| + 5·(n + 1) + 20` (`UniversalBlock.lean:750`). TMSAT's
public bridge `timed_universal_quantitative` (`ClassNP/TMSAT.lean:710`) bounds the whole
coefficient by `3|α| + 14·canonizerTime(|α|) + 50` (`tmsat_concrete_coefficient`, `:670`).
The step block's stated per-round `50·(|table| + 1)` is above `universalBlockBound`. It also
does not fit TMSAT's `14·canonizerTime` in general, since `|table|` can be close to
`canonizerTime(|α|)`. Even the sharper upper bound that the proof supports,
`T ≤ 7·|table| + 3q + |word| + 42` (§1.4), is above `universalBlockBound = 3|serialize| + …`
whenever the table dominates the header. Whether the *actual* round time fits is open: it is
at least about `2·|table|`, from one pass plus one rewind.

U-1 must therefore choose one of three courses:
* sharpen the block's time clause, which re-proves the ledger only (the trace components
  exist);
* restate the displayed coefficient, which needs a statement gate and TMSAT's re-check;
* keep the chapter-1 timed layer for the concrete form.

This is not a promotion blocker. Record it on U-1 (O8).

### 2.6 Summary

| Consumer | Verdict for the step block | What else it waits on |
|---|---|---|
| H1 | as is | its own items 4–6 (startup, Z1 and the clock, the ledger) |
| EXPCOM | as is (through H1) | H1 |
| B6 `U₀` / `SU` | as is, plus the additive `roundTM_visited` and `roundTM_iterate`, plus a host-side forward leaf | H3 (the windowed runner), H5 (`SU`'s device), `U₀`'s statement |
| C1 | as is (the lifted-table identity), plus a host-side choice installer | SC-3, H5 |
| U-1 | as is, except the frozen concrete constant (O8) | H5, the O8 decision |

None of the five consumers needs the block's statement changed.

---

## 3. Recommendation

### 3.1 Promote as is now, and generalize later

Move the proved declarations unchanged to a public module, and have H1 cite them. The reasons:

1. **No named consumer needs a block change** (§2.6). Emission, the choice bit and the input
   device are all met by host-side phases around the unchanged block. Space and iteration are
   additive corollaries, already proved from the contract in the draft.
2. **It costs no proof work.** The move is mechanical: rename, drop `private` on the public
   list, and change no proof body (§4.4, commit 1). It has been dry-run: the renamed move
   elaborates with 0 errors under the proposed imports (§4.1). The five additive results are
   written, and they elaborate against the proved contract.
3. **It unblocks the rule.** `workflow.md:129–133` says a private host already in the tree is
   harvested before a second consumer is briefed. Promotion is the gating step for U₀, C1 and
   U-1. The generalization designs belong with those consumers (rule of admission: two named
   customers per item).
4. **It avoids re-proving twice.** MIG-0b's round layer will restate rounds anyway (§3.3), and
   a generalization now would have to be migrated again.

### 3.2 The alternative: generalize at promotion

These are the candidate generalizations, with costs (ESTIMATE) and risks:

| Generalization | Who wants it | Cost (ESTIMATE) | Risk |
|---|---|---|---|
| An output-mode parameter (summary or emit) in the record phase | U₀, SU, U-1 | 600–1,000 proof lines touched. Every lemma about `h1RoundTM k` takes the mode; `h1Record_execute`, `_envelope`, `_effect`, `h1Round_payload`, `_canonical` and `_effect` change their output clauses. | Moderate to high: long `simp` traces over the unfolded payload. The move turns into a fill batch. **Superseded** by the forward-and-reset leaf. |
| A choice-indexed lookup | C1 | 500–800 lines (the selector, the table cut, the rank) | High. **Superseded** by `ndTable_eq_tableBitsK`. |
| A sharper or exact time clause | U-1 (TMSAT's constant), and MIG-0b's exact-time principle | 50–150 lines (the ledger only; the trace lemmas carry the components) | Low. It is additive as a sibling theorem, so it can come later. |

If the user prefers one generalization at promotion, the sharper time clause is the only one
with a real consumer and a low risk. It can be added as a *sibling* theorem without touching the
verbatim one.

### 3.3 The `Contract` phrasing, and how it migrates

* **Now: the existing style.** MIG-0a's `Turing.Contract` (`audits/evidence/mig0/
  Contract-draft.lean.txt:84–101`) is not landed. In any case it does not fit:
  - it is a first-exit contract whose cut includes time 0, but `entry` is itself an exit of
    the round;
  - `ReturnContract` (`:565–582`) has a single exit (`exit_eq`), but the round has two, `entry`
    and `halt`.

  The step block is exactly the **return-or-escape round** of MIG-0b item 2
  (`machine-library-design.md:3713`): positive cuts against the anchor and the escape. That
  layer is not designed yet.
* **Later: an adapter, with no re-proof.** When MIG-0b's round layer lands, add
  `roundTM_round : RoundContract (roundTM k) entry halt ι x` with:
  - `ι := Σ n, table × source configuration × state` and `pre := entry ∧ Rep ∧ live`;
  - `time :=` the first return time (`Nat.find` on the existential), and `post := runFrom`;
  - envelope intervals `[min, max]` of the start and end positions for mirrored heads, and
    `[-B, B]` for auxiliary heads.

  The existing-style theorem stays as its proof source. The derived space bound then comes from
  the structure (`spaceUsedByTape_le`), and `roundTM_visited` becomes a corollary.

---

## 4. The proposed public module

### 4.1 Home, name, namespace and imports

* **Home: `TCSlib/Complexity/TuringMachine/Build/StepBlock.lean`**, a Build-layer host file.
  It goes into the `TuringMachine.lean` facade's imports and its `## Contents` list.
* **Namespace: `Turing.StepBlock`**, with three exceptions:
  - `workReadsK` and `tableBitsK` keep their present names `Turing.workReadsK` and
    `Turing.tableBitsK`. They are moved, so no consumer changes.
  - The generic lemmas go in `Turing.MultiTapeTM`: `abs_workTapePos_runFrom_sub_le`,
    `inputPos_runFrom_of_inputTape_eq_zero`, `visitedByTapeHead_add_subset` and
    `visitedByTapeHead_step_subset`. The precedent is
    `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`, which lives in `Build/Catalog.lean:392`.
* **Imports: `CodeFormat`, `Build.Seam`, `Build.Catalog`. Confirmed by a dry run of the
  move.** `h2/work/moveprobe.py` extracts every declaration to be moved, with its proof
  verbatim, applies Appendix A's rename map, and places the result under exactly these three
  imports in namespace `Turing.StepBlock` (`h2/work/MoveProbe.lean`, 2,912 lines). It
  elaborates with **0 errors, 0 sorries, and the same 67 linter warnings** as the delivered
  region. Its contracts print the standard triple.

  The closure contains neither `CounterLoop` nor `VirtualInput` nor `CodeSimulator`. H2 sits
  below the hosts that drive it, so U₀ (SpaceComplexity) and C1 (NDCodes, NTimeHierarchy) can
  import it without `CodeSimulator`. That answers §12.11's closure remark
  (`machine-library-design.md:2416ff.`).

### 4.2 What moves (Appendix A has every name)

* **The layout** (`CodeSimulator.lean:85–101`): `workReadsK` and `tableBitsK`, 2 public
  declarations, names unchanged.
* **The summary** (`:1950–1999`): `outputSummary`, `summaryEmit`, `outputSummary_append`,
  `outputSummary_true` and `summaryEmit_other`. All 5 are private now and become public. The
  `summaryClock` family (`:2000–2038`, 4 declarations) **stays** in `CodeSimulator`: it is H1's
  semantics.
* **The step block** (`:2039–4867`): 114 private declarations, 2,829 lines.
  - **Public** (needed by the public statements, or useful to hosts that establish `Rep`):
    - the machines and their control types: `recordWidth`, `RecordState`, `tableTape`,
      `summaryTape`, `payload`, `applyPayload`, `recordTM`, `recordFinTM`, the ranks,
      `SuccPhase`, `succFieldTM`, `succFieldCfg`, `afterTag`, the skipper family, the
      selector family, `twoMoveTM`, `Key`, `Ph`, `part`, `exit`, `red`, `roundTM`,
      `roundFinTM`, `summaryCells` and `Rep`;
    - six instances;
    - the contracts: `recordTM_effect`, `succFieldTM_run`, `_cut` and `_heads`,
      `recordSkipTM_run` and `_spec`, `roundTM_effect`;
    - the layout lemmas `summaryCells_shift`, `_update`, `_copy` and `_clear`;
    - `mem_workReadsK`, `length_workReadsK` and the two generic `MultiTapeTM` lemmas.
  - **Private**: the trace internals, for example `readCfg`, `roundData`, `RoundSpan`,
    `seekCost`, the `_trace`, `_path` and `_many` lemmas, and `roundTM_canonical`.
* **Additive (new):** `summaryEmit_none`, `visitedByTapeHead_add_subset`,
  `visitedByTapeHead_step_subset`, `roundTM_visited` and `roundTM_iterate`. All five are proved
  in the draft. The last two depend on the contract only through its statement.

In all, 121 declarations move and 5 are added. About 70 are public: about 41 definitions, 6
instances and about 23 theorems.

### 4.3 What changes in `CodeSimulator.lean`

1. Add `import TCSlib.Complexity.TuringMachine.Build.StepBlock`. The other imports stay: the
   canonizer gap and H1's assembly still use them.
2. Delete `:85–101` (the layout definitions, now in StepBlock under the same names). The
   bridges `workReadsK_one`, `workReadsK_two`, `tableBitsK_two` and
   `codeSkipTable2_eq_codeSkipTableK` stay, unchanged.
3. Delete `:1950–1999` and `:2039–4867`. The H1 gap is then empty. **No private copy is kept.**
   F7-1(a) allows "H1's own assembly may continue on the private copy", but a kept copy would
   be about 2,880 lines of duplicated proved material, which policy §1 *Duplication* says
   needs human approval. The next H1 continuation cites the public names instead (O2).
4. In the `summaryClock` family, use the public names. `open StepBlock` (or qualified names)
   for `summaryEmit`, `outputSummary_append` and `outputSummary_true`. No proof changes.
5. Docstrings:
   - the module status (`:43–59`, the simulator bullet at `:51–55`) cites
     `Turing.StepBlock.roundTM_effect`;
   - the headline's two H1 fill appendices (`:4906` and `:4923`) replace the private names by
     the public ones (status text only).

The result is about 2,060 lines, down from 4,950. The public surface of `CodeSimulator` is
unchanged apart from the two moved layout definitions, which keep their names and statements.

### 4.4 The maintainer's PR, in three commits

The PR goes on a side branch, and the user merges it (plan decision log,
`AroraBarakChapters3-4Plan.md:682`: all changes go through PRs).

1. **The move, with the freeze check.** Create `Build/StepBlock.lean` from the extracted
   declarations, renamed by Appendix A's map, with `private` dropped on the public list and the
   public docstrings taken from the draft. Make the `CodeSimulator.lean` edits of §4.3, and
   update the facade.

   Check: every moved body is identical to its original modulo the rename map.
   `h2/work/fidelity.py` already does this for statements and definitions; the PR extends it to
   full proof bodies. `h2/work/moveprobe.py` is this commit's content minus visibility and
   docstrings, and it already elaborates (§4.1).
2. **The additive results.** Add the five additive declarations, with the draft's proofs. They
   use the contract only as stated. Appended to the dry run (`h2/work/MovePlusAdditive.lean`),
   they elaborate against the *proved* contract with 0 errors, and `roundTM_iterate` and
   `roundTM_visited` print the standard triple, with no `sorryAx`.
3. **Style.** Optional, and separately verified. Wrap the 101 lines over 100 columns in the
   moved region. Clear its 67 linter warnings: 41 unused `simp` arguments, 8 unreachable
   tactics, 7 `<;>` lints, 6 no-op `omega`s, 2 `simpa`s, 2 no-op `congr 1`s and 1 unused
   variable. These come from the read-only elaboration of `CodeSimulator.lean`, which gave
   0 errors, 2 sorries (lines 1945 and 4938) and 67 other warnings, all in `:2039–4867`. This
   is F7-1(e), and it falls to the maintainer, since the maintainer owns the new file.

### 4.5 The replay closure

The downstream modules of `CodeSimulator` were computed from the import graph
(`h2/work/rdeps.py`):
* `Codes2Tape`;
* `Diagonalization.EXPCOM`;
* `Diagonalization.Relativization`;
* the facades `TuringMachine` and `Diagonalization`;
* the root `TCSlib`.

Adding the new `Build.StepBlock`, the replay set is **8 modules including the root**. As in
earlier replays, the root needs non-campaign oleans.

Expected sorry sets, all unchanged:
* `CodeSimulator`: 2;
* StepBlock: 0;
* `Codes2Tape`, `EXPCOM` and `Relativization`: their present sets.

Two other placements would widen the closure:
* moving `workReadsK`/`tableBitsK` into `CodeFormat` instead: 23 downstream modules (O3);
* moving the run head bound into `Deterministic.lean`: nearly the whole library (O9).

### 4.6 The gate sequence

1. **H2-S, the statement gate** (round 1). The pack holds:
   - this note, `StepBlockDraft.lean` (as `.lean.txt`), `elaboration.log` and `fidelity.log`
     with its script, and the C1 probe;
   - the delivered `CodeSimulator.lean` and `h1-2-REPORT.md` (*Promotion candidate*);
   - every consumer file cited in §2: `CounterLoop`, `VirtualInput`, `EXPCOM`, the B6
     restatement evidence, `NTimeHierarchy`, `NDCodes`, `Universal`, `UniversalBlock`,
     `UniversalStartup`, `TMSAT` and the MIG-0a draft;
   - the standards: `audits/TEMPLATE.md`, `policy.md` and `workflow.md`.

   The auditor rules on:
   - (a) the renamed statements, which match the delivered ones (mechanical);
   - (b) the five consumer verdicts of §2;
   - (c) the homes, names, public/private split and docstrings (policy §2: natural-language
     statement first);
   - (d) the truth of the additive statements (proved modulo the contract);
   - (e) the `Contract` migration note.
2. **H2-M, the maintainer's PR** (§4.4), with verification:
   - the 8-module replay at 0 errors, with sorry sets unchanged;
   - the freeze check of commit 1;
   - axiom prints of every new public theorem, within `{propext, Classical.choice, Quot.sound}`;
   - lint at 0 FAIL;
   - a duplication screen showing no copy left in `CodeSimulator`.
3. **The H2-M gate.** The PR's own light gate: freeze, replay and fidelity. Design §16
   decision 2 (`machine-library-design.md:3546ff.`) gates proof moves under unchanged
   statements by a freeze check, a replay and a fidelity gate.
4. **After the close:**
   - registry row H2 becomes "public, gated" (`machine-library-design.md:3059`), and F7-1(a)
     is closed;
   - the next H1 continuation brief (items 4–6) cites `Turing.StepBlock.*`;
   - readiness checks for U₀ (RD-3), C1 and U-1 may then name H2 as a registered host, each
     with its host-side additions (§2).

---

## 5. Open questions

* **O1. Name collision.** `backlog.md:1354` calls the per-code-linear timed simulator "B5a
  headline **H2**", which is unrelated to host H2.
  *Recommendation:* rename that backlog item ("B5a linear headline", for example) in the PR's
  records.
* **O2. Timing against batches that own `CodeSimulator`.** The H1 continuation (items 4–6) and
  the canonizer continuation both live in this file.
  *Recommendation:* land H2-M between continuations, before either brief is reissued. If the
  canonizer continuation must run at the same time, carve the file out by declaration, as in the
  B5b `EXPCOM` precedent. The move touches only `:43–59`, `:85–101`, `:1950–1999`,
  `:2039–4867` and the headline docstring (`:4869–4937`); the canonizer gap is `:196–1948`.
* **O3. Home of `workReadsK`/`tableBitsK`.** They could go to StepBlock (8-module replay) or to
  `CodeFormat`, their natural home next to `actionBitsK` (23 downstream modules).
  *Recommendation:* StepBlock now, and `CodeFormat` at a later shared-file window.
* **O4. Three summary encodings.**
  - this cell code (`Option Bool`);
  - `Turing.OutSummary`/`outSummary` (`SpaceComplexity/ConfigGraph.lean:104–121`);
  - the record rows' `Fin 3` (§12.8a O4).

  *Recommendation:* promote the cell code as is. Record a dedup item, owned by the maintainer:
  move `OutSummary` down into Build, with a bridge `outputSummary w = toCell (outSummary w)`.
* **O5. Public surface.** About 70 public declarations, because the state type is a Σ over the
  phase family. An opaque `StepBlock.State k` with public `entry` and `halt` would hide the
  selector and the phases, but it changes the statement's text.
  *Recommendation:* not now. Revisit with MIG-0b's adapter.
* **O6. The additive results in the PR.**
  *Recommendation:* include them. They are small (about 200 lines), already proved, and they
  are what U₀ and U-1 will cite. If the gate wants a minimal surface, move them to the first
  consumer's batch instead.
* **O7. A `roundTime` function** (the first return time) for `counterLoopTM`'s `τ` and for
  MIG-0b's `time`.
  *Recommendation:* add it with the MIG-0b adapter. H1 can choose for now.
* **O8. U-1's frozen constant** (§2.5).
  *Recommendation:* record it on backlog U-1/MIG-2 now: "the step block's stated round bound
  exceeds `universalBlockBound`; choose among sharpening, restating, or keeping the chapter-1
  timed layer". No action at promotion.
* **O9. Home of the run head bound.** `Deterministic.lean` is the natural home, but the replay
  would cover nearly the whole library.
  *Recommendation:* StepBlock now, as `Turing.MultiTapeTM.abs_workTapePos_runFrom_sub_le`, and
  `Deterministic.lean` with MIG-1. Likewise for `h1Run_input` and the two visited lemmas.
* **O10. Style debt** (F7-1(e)).
  *Recommendation:* fix it in commit 3 of H2-M, after the freeze-checked move.
* **O11. A requirement on H5.** Every input device must transform a native-input machine in
  lockstep, as Z1 does, so that `Rep`'s native input clause transports.
  *Recommendation:* write this into H5's design as a requirement.
* **O12. F7-1(c), the fixed-field walk.** The canonizer's remaining record parser walks the same
  fixed fields as the reader.
  *Recommendation:* the canonizer continuation cites the public `recordTM`/`recordTM_effect`
  where they fit, instead of factoring a third walk.

---

## 6. Size estimate (ESTIMATE)

* **New `Build/StepBlock.lean`, about 3,350 lines:**
  - about 2,900 moved;
  - about 250 of header and public-docstring growth;
  - about 200 additive.

  This is reported per the size rule, with no split proposed. A split into Record, Seek and
  Round is possible if the gate wants one.
* **`CodeSimulator.lean`, about 2,060 lines** (from 4,950).
* **Net change: about +450 lines.**
* **Effort:**
  - the statement gate: one round, since the statements are verbatim and the definitions are
    copied;
  - H2-M: a scripted move, already dry-run, plus about 200 lines already written, with an
    8-module replay;
  - the H2-M gate: light.

The rejected alternative, generalizing at promotion, adds a fill batch of about 1,150–1,950
proof lines touched (§3.2, ESTIMATE).

---

## 7. Evidence produced for this note (all in `h2/`)

* `StepBlockDraft.lean` is the proposed public statements, about 960 lines. Its definitions
  are copied under `Turing.Draft.StepBlock`, and seven contracts are sorried.
  - **0 errors, 7 sorry warnings, 0 other warnings** (`elaboration.log`).
  - All lines are within 100 columns.
* `fidelity.log`: **58/58** copied declarations match their originals after renaming:
  - definitions in full;
  - theorems by statement, and in full where the proof is copied.

  A negative control with two mutations gives two `DIFFER`s. There is **no definition that
  could not be copied faithfully.** The only liberties are these, all checked mechanically:
  - names, per Appendix A;
  - `private` removed;
  - `lemma` changed to `theorem` for the component contracts;
  - line wrapping;
  - new docstrings.
* The axiom probe (appended to `elaboration.log`):
  - definitions and proved lemmas are within the standard triple;
  - `roundTM_visited` and `roundTM_iterate` add `sorryAx` only through `roundTM_effect`.
* `probe/C1LiftProbe.lean`, `ndTable_eq_tableBitsK`: **0 errors, 0 warnings**.
* `work/codesim-elab.txt`: the delivered `CodeSimulator.lean` elaborates on `oleans-f7` with
  0 errors, 2 sorries and 67 linter warnings.
* `work/MoveProbe.lean`, generated by `work/moveprobe.py`, is the **dry run of the move**:
  - all 121 declarations, proofs verbatim, renamed by Appendix A (an injective map, with no
    `h1` name left);
  - the three proposed imports;
  - **0 errors, 0 sorries, the 67 inherited linter warnings**; the contracts print the
    standard triple.
* `work/MovePlusAdditive.lean` is the dry run plus the draft's additive results: **0 errors**,
  and `roundTM_iterate` and `roundTM_visited` are sorry-free (the standard triple).
* `work/`: the scripts, run with `python3 -I`:
  - `fidelity.py`, the freeze-check basis;
  - `rdeps.py` and `fdeps.py`, the replay closure;
  - `idents.py`, the external identifiers of the moved proofs;
  - `ImportProbe.lean`, the import set.

---

## Appendix A. The rename map

The **public** names are proposed for the gate. The **private** names are the maintainer's
choice: any injective map serves the freeze check, and this one avoids keywords (`at`, for
example).

| Original (`CodeSimulator.lean`) | Proposed | Visibility |
|---|---|---|
| `workReadsK`, `tableBitsK` | unchanged (`Turing.`) | public, moved |
| `outputSummary`, `summaryEmit`, `outputSummary_append`, `outputSummary_true`, `summaryEmit_other` | `StepBlock.` + same | public |
| `h1RecordWidth`, `h1RecordState`, `h1TableTape`, `h1SummaryTape` | `recordWidth`, `RecordState`, `tableTape`, `summaryTape` | public |
| `h1Mirror_ne_table`, `h1Summary_ne_table`, `h1Mirror_ne_summary` | `mirror_ne_table`, `summary_ne_table`, `mirror_ne_summary` | private |
| `h1Payload`, `h1ApplyPayload`, `h1RecordTM`, `h1RecordFinTM` | `payload`, `applyPayload`, `recordTM`, `recordFinTM` | public |
| `h1ReadCfg`, `h1Payload_correct`, `h1Record_read`, `h1Record_execute`, `h1Record_envelope` | `readCfg`, `payload_correct`, `recordTM_read`, `recordTM_execute`, `recordTM_envelope` | private |
| `h1Record_effect` | `recordTM_effect` | public |
| `h1WorkReads_mem`, `h1WorkReads_length` | `mem_workReadsK`, `length_workReadsK` | public |
| `h1WorkRank`, `h1InputRank`, `h1ReadRank` | `workRank`, `inputRank`, `readRank` | public |
| `h1SuccPhase`, `h1SuccTM`, `h1UnaryCfg`, `h1AfterTag` | `SuccPhase`, `succFieldTM`, `succFieldCfg`, `afterTag` | public |
| `h1Unary_step`, `h1Unary_run`, `h1Succ_trace` | `succFieldTM_unary_step`, `succFieldTM_unary_run`, `succFieldTM_trace` | private |
| `h1Succ_run`, `h1Succ_cut`, `h1Succ_heads` | `succFieldTM_run`, `succFieldTM_cut`, `succFieldTM_heads` | public |
| `h1SkipPh`, `h1SkipPart`, `h1SkipRed`, `h1SkipTM` | `SkipPh`, `skipPart`, `skipRed`, `recordSkipTM` | public |
| `h1Skip_fixed`, `h1Skip_tail`, `h1Action_split`, `h1Reads_append`, `h1Action_reads`, `h1Skip_path` | `recordSkipTM_fixed`, `recordSkipTM_tail`, `actionBitsK_split`, `reads_append`, `actionBitsK_reads`, `recordSkipTM_path` | private |
| `h1Skip_run`, `h1Skip_spec` | `recordSkipTM_run`, `recordSkipTM_spec` | public |
| `h1SkipPh_finite`, `h1SkipPh_decidable` | `instFintypeSkipPh`, `instDecidableEqSkipPh` | public instances |
| `h1SeekCtrl`, `h1SeekRouter`, `h1SeekNext`, `h1SeekKey`, `h1SeekPh`, `h1SeekPart`, `h1SeekRed`, `h1SeekTM` | `SeekCtrl`, `seekRouterTM`, `seekNext`, `SeekKey`, `SeekPh`, `seekPart`, `seekRed`, `seekTM` | public |
| `h1SeekCfg`, `h1Seek_request`, `h1SeekCost`, `h1Seek_many`, `h1Seek_stateStep`, `h1Seek_rank`, `h1SeekShift`, `h1Seek_groups`, `h1Seek_observe`, `h1Seek_lookup`, `h1Seek_select` | `seekCfg`, `seekTM_request`, `seekCost`, `seekTM_many`, `seekTM_stateStep`, `seekTM_rank`, `seekShift`, `seekTM_groups`, `seekTM_observe`, `seekTM_lookup`, `seekTM_select` | private |
| `h1ReadActions`, `h1ReadActions_length`, `h1ReadActions_at`, `h1Table_groups`, `h1Table_cut`, `h1Records_length`, `h1Groups_length` | `readActions`, `readActions_length`, `readActions_at`, `tableBitsK_groups`, `tableBitsK_cut`, `records_length`, `groups_length` | private |
| `h1Run_headBound`, `h1Run_input` | `MultiTapeTM.abs_workTapePos_runFrom_sub_le`, `MultiTapeTM.inputPos_runFrom_of_inputTape_eq_zero` | public |
| `h1Unary_read`, `h1Buffer_outside`, `h1Buffer_reads`, `h1Buffer_suffix` | `bufferTape_unary`, `bufferTape_outside`, `bufferTape_reads`, `bufferTape_suffix` | private |
| `h1SummaryState`, `h1SummaryState_cell`, `_update`, `_copy`, `_clear` | `summaryCells`, `summaryCells_shift`, `_update`, `_copy`, `_clear` | public |
| `h1TwoMoveTM`, `h1TwoMove_run` | `twoMoveTM` (public), `twoMoveTM_run` (private) | mixed |
| `h1SeekPh_finite`, `h1SeekPh_decidable`, `h1RoundPh_finite`, `h1RoundPh_decidable` | `instFintypeSeekPh`, `instDecidableEqSeekPh`, `instFintypePh`, `instDecidableEqPh` | public instances |
| `h1RoundKey`, `h1RoundPh`, `h1RoundPart`, `h1RoundExit`, `h1RoundRed`, `h1RoundTM`, `h1RoundFinTM` | `Key`, `Ph`, `part`, `exit`, `red`, `roundTM`, `roundFinTM` | public |
| `h1Data`, `h1Data_shift`, `h1RoundWindow`, `h1Data_window`, `h1RoundSpan`, `h1RoundSpan_add`, `h1Round_phase`, `h1At`, `h1Window_frame`, `h1Data_stateCell` | `roundData`, `roundData_shift`, `RoundWindow`, `roundData_window`, `RoundSpan`, `RoundSpan.add`, `roundTM_phase`, `atKey`, `roundWindow_frame`, `roundData_stateCell` | private |
| `h1Round_prepare`, `h1Round_payload`, `h1Round_restore`, `h1Round_lookup`, `h1Round_canonical`, `h1RoundRep_entry` | `roundTM_prepare`, `roundTM_payload`, `roundTM_restore`, `roundTM_lookup`, `roundTM_canonical`, `rep_entry` | private |
| `h1RoundRep`, `h1Round_effect` | `Rep`, `roundTM_effect` | public |
| (new) | `summaryEmit_none`, `MultiTapeTM.visitedByTapeHead_add_subset`, `MultiTapeTM.visitedByTapeHead_step_subset`, `roundTM_visited`, `roundTM_iterate` | public, additive |

## Appendix B. Verification commands (read-only)

```
S=<scratchpad>
bash $S/tools/leanelab.sh $S/wt-h2 $S/oleans-f7 $S/h2/StepBlockDraft.lean
bash $S/tools/leanelab.sh $S/wt-h2 $S/oleans-f7 $S/h2/probe/C1LiftProbe.lean
python3 -I $S/h2/work/fidelity.py $S/wt-h2 $S/h2/StepBlockDraft.lean
python3 -I $S/h2/work/rdeps.py $S/wt-h2 TCSlib.Complexity.TuringMachine.CodeSimulator
python3 -I $S/h2/work/moveprobe.py $S/wt-h2 $S/h2/work/MoveProbe.lean
bash $S/tools/leanelab.sh $S/wt-h2 $S/oleans-f7 $S/h2/work/MoveProbe.lean
bash $S/tools/leanelab.sh $S/wt-h2 $S/oleans-f7 $S/h2/work/MovePlusAdditive.lean
```
