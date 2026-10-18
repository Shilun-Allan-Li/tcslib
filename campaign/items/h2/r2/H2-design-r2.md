# H2: promoting the step block. Design note, round 2 (revised)

Maintainer draft (sub-agent), 2026-10-14, for round 2 of the H2-S statement gate. **This is the
revised note.** It is the round-1 note (`audits/evidence/h2/H2-design.md`) brought up to round
2 throughout: every changed passage is marked **[r2]**, and §0 lists every change with the
finding it answers. The round-1 note stays in the repository unchanged.

It was written read-only against the checkout `wt-r2h2` at **campaign commit 1781a230** (PR #84,
fills-8), elaborating against `oleans-f8` (all of TCSlib at that commit). Every `file:line`
below is at 1781a230; a bare `:N` means `TuringMachine/CodeSimulator.lean:N`. `h2/r2/` means
this round's evidence directory, `audits/evidence/h2/r2/`. Figures are labelled MEASURED
(computed by a script or by Lean, with the log named) or ESTIMATE.

**Recommendation, unchanged: promote as is.** The seven copied contracts are unchanged, in code,
from round 1 (`fidelity-r2-pass.log`: 58 of 58 copied declarations byte-identical to the
round-1 draft, and faithful to `CodeSimulator.lean` at 1781a230). Round 2 repairs the advertised
consumer interface (finding 1), the H5 requirement (finding 2), the evidence (finding 3) and
the records (minors 4–8), and adds the H2-M text edits that the H1 continuation escalated
(§4.7).

Contents:
0. What changed in round 2
1. The delivered contract
2. What each named consumer needs, with a verdict
3. Recommendation; `Contract` phrasing and migration
4. The public module, the `CodeSimulator.lean` changes, the replay closure, the gates, the
   H2-M text edits
5. Open questions
6. Size and splitting (layering and consumer reasons only)
7. Evidence

Appendix A gives the rename map with the round-2 visibility, Appendix B the commands.

---

## 0. What changed in round 2 [r2]

| Finding (round 1) | Where | Change |
|---|---|---|
| 1 (major): `roundTM_iterate` lacks cofinality | draft; §§1.4, 2.3, 2.5 | Restated with `t ≤ T ≤ t·B`, **proved** (in the draft modulo the sorried contract; against the proved contract in `MovePlusAdditive-r2.lean`, standard axioms). New additive `roundTM_firstExit_unique` (the round time is the unique first positive exit). The reset/forward wrapper is the named consumer obligation **CO-RF** (§2.3b), not an H2 theorem. The seven copied contracts are unchanged. |
| 2 (major): H5 as literal lockstep | §§1.4, 2.3, 2.3a, 2.4, 2.5, O11 | H5's requirement is now a **positive, finite block simulation** of a native-input machine (frames, output, exit cuts, head envelopes), with literal lockstep as the Z1/native special case and separate resource guarantees per consumer. The B6 draft's ruler host and the user's 2026-10-13 decisions are taken in. |
| 3 (major): missing sources and manifest | §§2.5, 3.3, 4.5, 4.6; bundle | The consumer sources are bundled (§7). The import manifest is computed by `importclosure.py` from the checkout's `import` lines (`importclosure.out`, `import-graph.txt`). The probes already run are distinguished from the H2-M replay still to come (§4.6). |
| 4 (minor): reset output invariant | §2.3b | CO-RF stated in the auditor's form; its data-level steps are checked by a probe (`ResetProbe`). |
| 5 (minor): ownership manifest | §4.3 | A declaration-based manifest, computed by name by `movemanifest.py` **at the integration base 1781a230**, covering imports, the summary-clock family, the H1 clock delivered by fills-8, status text and every H1 reference. |
| 6 (minor): `fidelity.py` | §7 | `fidelity-r2.py`: nonzero exit on any mismatch, missing, extra or duplicate declaration and on any unexpected addition; full inventory asserted; additives whitelisted; seven negative controls. |
| 7 (minor): size | §6 | Answered by layering and consumer reasons, under the user's rule that size alone never justifies a split. |
| 8 (minor): descriptions | §§1.1, 1.2, 4.4, 7; draft | The bound depends on the table; `Key` has 15 constructors and 20 values; line lengths are counted in Unicode characters; the axiom claim is qualified; the additive count is corrected (now six). |
| O5 ruling | §4.2 | A narrower surface without changing any contract: 15 implementation helpers become private (round-1 surface 70 names, round-2 56). |
| Integration base (coordinator) | §§1.5, 4.3, 4.7 | Recomputed at 1781a230. H1's cleanup rewrote 24 step-block proof bodies (no statement); the round-1 move probe is stale for those. The H1 escalation (14 over-width lines in frozen text, the unused binder `hr`) is handled in the H2-M move by whitespace re-wrapping and the binder renamed `_hr`: no statement changes, up to α-equivalence, checked mechanically. |

---

## 1. The delivered contract

### 1.1 Setting

The private host lives in `TCSlib/Complexity/TuringMachine/CodeSimulator.lean` (6,230 lines at
1781a230, MEASURED), namespace `Turing.MachineFormat`. None of its declarations uses the section
variable `F`. It is one finite machine per work-tape count `k`:

* **`h1RoundTM k : MultiTapeTM (k + 2) Bool (Σ key, h1RoundPh k key)`** (`:4809`). This is
  `phaseHostTM` over the schedule `h1RoundKey` (`:4749`) **[r2] with 15 constructors and 20
  values (five constructors carry the live bit)**; `h1RoundPart` (`:4769`); `h1RoundRed`
  (`:4789`). The schedule runs as follows:
  - lookup, by the selector `h1SeekTM` (`:3829`), itself a phase host over a router and the
    whole-record skipper;
  - clear the old state word, using catalog `skipTM`, `skipBackTM` and `clearTM`;
  - read and execute the record's fixed fields (`h1RecordTM`, `:2910`);
  - install the successor (`h1SuccTM`, `:3268`);
  - restore both auxiliary heads.

  Its control types depend only on `k` (`h1RoundPh_finite`, `:4813`).
* **The tapes.** Work tapes `0..k-1` mirror the simulated machine's work tapes. Tape `k`
  holds the table word. Tape `k + 1` holds the output summary at cell 0, a blank at cell 1, and
  the current state in unary from cell 2 on (`h1SummaryState`, `:4593`).
* **The exits** (`h1RoundExit`, `:4784`): `⟨.entry, ()⟩`, which is also the start state, and
  `⟨.halt, ()⟩`. Both are live states, and `.halt` is stationary.

### 1.2 `h1Round_effect` (`:5657`) in mathematical English

Fix a transition table `tr` of a `k`-work-tape binary machine with `n + 1` states, an input
`x`, a live source configuration `c` on `x` in state `q`, and let `a = tr(q, input read of c,
work reads of c)`. Let `d` be a configuration of the step block on the **same input `x`**,
at `entry`, that **represents** `c` (`h1RoundRep`, `:5599`):
* the native input head of `d` is at `c`'s input position;
* the first `k` tapes and heads of `d` are `c`'s;
* tape `k` holds `tableBitsK tr` as a buffer word;
* tape `k + 1` holds `summaryCells(outputSummary(c.output), unary(q))`;
* both auxiliary heads are at cell 0.

`Rep` leaves the control state and the physical output of `d` free (the contract separately
assumes `d` at `entry`).

Then there is a time `T` with `0 < T ≤ 50·(|tableBitsK tr| + 1)` such that, writing `e` for the
configuration at time `T`:
1. **Endpoint.** `e` is at `entry` if `a` has a successor and at `halt` otherwise; it
   represents `a.apply c`; its summary cell is `summaryEmit(old summary, a.output)`.
2. **Cut.** Strictly between 0 and `T` the block is live and at neither exit.
3. **Silence.** The physical output equals `d.output` at every time up to `T`.
4. **Head envelope**, at every time `u ≤ T`: the input head and each mirrored head are at their
   start or end position, within one cell of the start; each auxiliary head is within
   `50·(|tableBitsK tr| + 1)` cells of its start.
5. **Home.** Both auxiliary heads are at cell 0 at time 0 and at time `T`.

**[r2] The bound depends on the table only, through `|tableBitsK tr|`, and so indirectly on
`k`, `n` and the table's actions; only the coefficient `50` is uniform.** It does not depend on
the input `x`, the tape contents or the simulated time. (Round 1 said "does not depend on `k`,
`n`"; finding 8.)

The endpoint is determined (`Rep` fixes every tape and head, the exit the control, silence the
output). Only `T` is existential, and **[r2] it is unique: `roundTM_firstExit_unique` (draft)
proves that exactly one positive time is a first visit to `entry` or `halt`**, so any witness
of the contract is that time.

### 1.3 The other promotion candidates

* **Whole-record skipper** (`h1SkipTM`, `:3501`): `h1Skip_run` (`:3621`), the endpoint after
  exactly `|actionBitsK a| + 1` steps, only the table head changed; `h1Skip_spec` (`:3738`), no
  exit earlier, and the exact table-head displacement at every time.
* **Successor-field leaf** (`h1SuccTM`): `h1Succ_run` (`:3430`), `h1Succ_cut` (`:3442`),
  `h1Succ_heads` (`:3458`).
* **Fixed-field reader** (`h1Record_effect`, `:3155`): exactly `4k + 5` steps, a framed effect
  and an envelope. It assumes canonical action bits and executes the payload: it is not a
  validator (round-1 ruling on O12).
* **Run head bound** (`h1Run_headBound`, `:4466`).

### 1.4 What the contract does not state

| Missing clause | Status |
|---|---|
| **Space** | Derivable from the envelope: the additive `roundTM_visited` (per round) and `roundTM_iterate` (over runs). |
| **Input device** | **Native only. [r2]** Any other input is supplied by an H5 device that is a positive, finite **block simulation** of a native-input machine (§2.3a); literal lockstep (Z1, the native device) is its special case. Not a step-block clause. |
| **Choice bit** | None needed; §2.4. |
| **Output** | **Summary, not emission.** `summaryEmit none b = b` (`summaryEmit_none`). **[r2]** A host that blanks the cell and forwards the emission needs its own invariant: the consumer obligation CO-RF (§2.3b). |
| **Exact time** | Only `0 < T ≤ 50·(|table| + 1)`; the proof's components give more (`h1Round_canonical`, `:5518`; lookup `h1Round_lookup`, `:5469`). |
| **Composition over rounds** | **[r2]** The additive `roundTM_iterate`, now with `t ≤ T ≤ t·B` (cofinal), for the *silent* block. |
| **Halting** | The block never halts physically; `halt` is a live, stationary exit. |
| **Validation** | None; the table must be exactly `tableBitsK tr`. |
| **`Contract` form** | Not stated in that form; §3.3. |

### 1.5 The integration base [r2]

Fills-8 (`audits/fills-8-integration.md`) integrated the canonizer's continuation 2 and H1's
continuation 2 into `CodeSimulator.lean`. For this promotion (all MEASURED, `movemanifest.out`
unless noted):
- the 121 declarations to move are all present, located by name, in three regions (`:89–104`,
  `:2771–2812`, `:2853–5750`); 226 declarations in all, 105 stay;
- **H1's new private assembly** (11 declarations, `:5752–6132`: the binary clock `h1ClockTM`,
  the round-time index `h1RoundTime` and `h1RoundTime_spec`, the orbit, round and clock
  lemmas, the hosted clock and its verdict) **cites `h1Round_effect` and the block's types**. It
  stays in `CodeSimulator.lean`; its references are renamed by the move (§4.3);
- H1's style cleanup rewrote the code of **exactly 24** step-block declarations: in 12 the
  proof body changed at the token level, in 12 only whitespace or comments changed; **no
  statement or definition changed** (`movemanifest.out`, comparison with the round-1 dry run,
  allowance list = the 24 names; the unallowed comparison `movemanifest-vs-r1-strict.out` shows
  exactly the 12);
- the inherited linter warnings fell from 67 to 1 (the binder `hr` of `h1Seek_stateStep`), and
  the step block's over-width lines from 83 to 14 (`linelen.out`; fills-8 record). Both remnants
  are in frozen text, escalated by H1 (`h1-3-escalation-excerpt.md`) and handled in §4.7.

---

## 2. The named consumers

Verdict grades: **as is**; **small generalization** (an additive lemma, or a sharper clause
whose proof exists in the components); **separate host**.

### 2.1 H1, `MachineFormat.exists_uniformSimulator` (`:6218`)

**Verdict: as is, now demonstrated. [r2]** H1's continuation 2 built its binary deadline clock
on the frozen block (`h1Clock_effect`, `:5880`), hosted it on Z1 (`h1HostedClock_effect`,
`:5984`) and derived the one-bit verdict (`h1HostedVerdict_accepts`, `:6115`), citing
`h1Round_effect`, `counterLoopTM_run_done`/`_escape` (`Build/CounterLoop.lean:1383`, `:1445`)
and `vhostEmitTM_runFrom` (`Build/VirtualInput.lean:243`) without re-deriving them. The first
named consumer has therefore consumed the contract unchanged.

Its round-time function `h1RoundTime` (`CodeSimulator.lean:5764`) is round 1's O7, defined by
`Nat.find` on the first positive exit; `h1RoundTime_spec` (`:5776`) re-proves inline (its `least` step) the
uniqueness that the additive `roundTM_firstExit_unique` states. See O7 (§5).

### 2.2 EXPCOM

EXPCOM consumes H1 only (`Diagonalization/EXPCOM.lean`, `exists_uniformMachineCode`). **As is,
through H1 at `k = 1`.**

### 2.3 B6's `U₀`, and `space_universal`'s `SU` (RD-3) [r2]

The window route runs one self-applying `U₀` on the native input, with one coded work tape and
the step block on the canonical table (the B6 host draft, `audits/evidence/b6hosts/`:
`exists_selfStartupTM`, `B6HostsDraft.lean.txt:1291`; `exists_selfUniversal`, `:1333`).

| Need | Verdict |
|---|---|
| `k = 1` and the one-tape code table | **as is** (`oneTapeMachineFormat.serialize_eq`: the table is `tableBitsK`). |
| Native input device | **as is**: under self-application the input is the simulated input, which is `Rep`'s input clause. |
| The same output, verbatim | **as is, plus a host-side wrapper with its own invariant (CO-RF, §2.3b)**. The block is unchanged. |
| Space ledger `C_α·(s + 1)` | **small generalization (additive, proved)**: `roundTM_visited`, `roundTM_iterate`. The wrapper's ledger is part of CO-RF. |
| An unclocked run until halt | **small generalization (additive, proved)**: `roundTM_iterate`, now cofinal (`t ≤ T`), for every live prefix; the final, halting round is `roundTM_effect` once more; CO-RF forwards its emission before the physical halt. |
| `SU` only: input `⟨bits s, ⟨α, x⟩⟩` | **separate host (H5): the ruler device** (§2.3a). By the user's decision of 2026-10-13 (`machine-library-design.md:3886`), `space_universal` is strengthened to `C·s` through the ruler device in the B6 hosts' gate, and **no binary-position device is stated**. |

### 2.3a H5: a positive, finite block simulation [r2] (finding 2)

Round 1 required every input device to transform a native-input machine "in lockstep, as Z1
does". The auditor showed that this does not fit a device whose virtual move costs several host
steps (a binary position counter's carry; equally the ruler's boundary test). **Revised
requirement on H5**, to be written into H5's design and stated in its gate:

> An input device presents a native-input source machine `M` on a physical input `z`. It is a
> host `H` with a presentation relation `Pres(c, d)` between source configurations `c` (on the
> virtual input `y`) and host configurations `d`, such that for every presented `c`:
> 1. **Positive, finite block.** If `c` is live, there is a block length `L` with
>    `1 ≤ L ≤ B_D`, where `B_D` depends on the device's parameters (for the ruler, `C·(ℓ + 1)`
>    with `ℓ` the header length) but not on the source time, such that
>    `Pres(M.step c, H.runFrom d L)`. A halted `c` is presented by a halted `d`.
> 2. **Intermediate frames.** At every time `u < L` the host is live and at no block-boundary
>    state; every bank tape is `c`'s or `M.step c`'s, with its head at its start or end position;
>    the device's own tapes stay within the device envelope.
> 3. **Output.** The physical output during the block is `c`'s output followed by at most the
>    source's one emission, and at the block's end it is `M.step c`'s.
> 4. **Exit cuts.** The host halts exactly at the block in which the source halts, never inside
>    a block of a live step.
> 5. **Head envelopes.** Bank tape `i` visits exactly the cells the source's tape `i` visits;
>    the device's tapes visit only the device's own cells.
>
> Iterating the blocks gives the checkpoint form `∀ t, ∃ T, t ≤ T ≤ S + B_D·t` with
> `Pres(M.runFrom c t, H.runFrom d T)`: the pattern of `UniversalInterpreter.universal_block_run`
> (`TuringMachine/UniversalInterpreter.lean:859`), whose lower bound is exactly finding 1's.

**Literal lockstep is the special case `L = 1`:** Z1's `vhostEmitTM_step` / `_runFrom`
(`Build/VirtualInput.lean:188`, `:243`) and the native device (`H = M`, `Pres` the identity).
`Rep`'s native input clause transports through any such device because the step block is the
*source* machine `M` (or part of it): the device runs the whole interpreter, one interpreter
step per block. The block itself never calls the device.

**The B6 draft's ruler host fits, as a checkpoint statement.** `exists_rulerHostTM`
(`B6HostsDraft.lean.txt:1244`) states: for every `t`, within `C·(ℓ + 1)·t` host steps the host
presents the source after `t` steps, bank visits equal, ruler visits within its two delimiters.
That is the iterated form above without the lower bound. Since the host halts only when the
source does and the output is append-only, its checkpoints already pin liveness and output
between checkpoints. **Recommendations for the H5 gate** (records, not H2 edits): add `t ≤ t'`
to `exists_rulerHostTM`'s conclusion, or state the one-block form (items 1–5) and derive the
iterated one; and correct the stale "binary-position" mentions of `machine-library-design.md`
(`:1429`, `:3858`; the registry row `:3066` stays, by the user's decision).

**Resource guarantees, per consumer** (H5 states each separately):

| Consumer | Device | Guarantee needed |
|---|---|---|
| H1 (B5a) | Z1, buffered (`vhostEmitTM`) | lockstep; time one host step per source step |
| B6 `U₀` | native | none beyond `Rep` (the identity device) |
| B6 `SU` (`space_universal`, `C·s`) | ruler | **space**: bank visits equal the source's; ruler `ℓ + 2` cells, with `ℓ ≤ (2|α| + 6)·s` (`B6-hosts-design.md` §4). No logarithmic position counter: no binary-position device is stated (user, 2026-10-13). Time unconstrained (forward-only). |
| C1 (`exists_timed_universal_NDTM`, `Diagonalization/NTimeHierarchy.lean:121`) | ruler or Z1 | **time**: per source step at most a per-code constant, so that `C·(t + 1)` survives (the ruler's `C·(ℓ + 1)` is per code when `ℓ` depends on `α` only) |
| U-1 (`universal`, `timed_universal`) | ruler (replacing `universalInput_read`/`_move`, `UniversalStartup.lean:338`, `:373`) | **time** per code as for C1, **and cofinality** (`t ≤ T`): the converse of `universal` needs divergence preserved |

### 2.3b Consumer obligation CO-RF: the reset/forward wrapper [r2] (finding 4, minor 4)

`roundTM_iterate` is about the silent block. A consumer that needs the real output (`U₀`,
U-1) wraps each round in a reset and a forward. **CO-RF, in the auditor's form**, is an
obligation of that consumer's fill (B6's `exists_selfUniversal`; U-1), not an H2 theorem:

1. **The seam relation.** At every reset seam the host configuration `d` satisfies
   `Rep tr {c with output := []} d`, where `c` is the source configuration; the real cumulative
   output `c.output` is tracked separately, in the host's physical output (or a buffer tape for
   `timed_universal`).
2. **Reset.** Blanking summary cell 0 turns `Rep tr c d` into `Rep tr {c with output := []} d'`
   (`summaryCells_update` with `none`). This is the step the auditor's counterexample (output
   `[true]`) rules out for the unerased `c`.
3. **Round.** Erasing the output changes neither the state nor the reads, so the source selects
   the same action `a`; and `a.apply {c with output := []} = {a.apply c with output :=
   a.output.toList}`. The unchanged contract applies to the erased configuration and leaves the
   cell at `summaryEmit none a.output = a.output` (`summaryEmit_none`).
4. **Forward.** The wrapper emits `a.output` physically, exactly once, then blanks the cell
   again, re-establishing item 1 for `M.step c`. The reset and forward leaves keep every head
   stationary (the summary head is at cell 0 at every seam, by `Rep`), so they add nothing to
   the visited sets; their configuration transport and control cuts must still be proved.
5. **The halting round.** On the round that ends at `halt`, the forward happens **before** the
   physical halt, so the final emission is not lost.
6. **The ledger.** The space ledger (`roundTM_visited`/`roundTM_iterate` plus the startup) is
   transported through the wrapper; its time is the rounds' plus `O(1)` per round.

**Evidence for steps 2–3** (data-level only): `h2/r2/ResetProbe-tail.lean.txt`, appended to a
copy of the draft, proves `probe_rep_reset` (step 2), `probe_reset_action` (step 3: same state
and reads, and the `apply` identity) and `probe_cell_after_reset` (step 3's cell value), with 0
errors and the standard axioms (`elaboration.log`, `ResetProbe`). These are probes, not
proposed surface. Recommended home of the record: CO-RF is added to `U₀`'s sketch and to
U-1's backlog entry at H2-M.

### 2.4 C1, the NTIME hierarchy

Unchanged from round 1, except **[r2] in-place input: an H5 block-simulation device preserving
C1's time bound (§2.3a), not a literal-lockstep device.** The table identity
`ndTable_eq_tableBitsK` (round-1 C1 probe) stands; the choice installer, the nondeterministic
host (SC-3), branch alignment and the amortized clock remain separate obligations (round-1
NF5).

### 2.5 U-1, re-deriving the chapter-1 universal machine (`backlog.md:424`)

| Need | Verdict |
|---|---|
| Output: verbatim (`universal`), buffered then `true :: buffer` or `[false]` (`timed_universal`) | **as is, host-side: CO-RF** (§2.3b), forwarding to the output or to a buffer tape |
| Per-code linear, no `|x|` and no `t` in a round | **as is, qualitatively** |
| The converse (divergence preserved) | **[r2] small generalization (additive, proved): `roundTM_iterate`'s cofinal form** `t ≤ T`, plus the device's cofinality (§2.3a) and CO-RF |
| In-place suffix input at `O(1)` per move | **[r2] separate host (H5)**: a block-simulation device with a per-code time constant and cofinality |
| **The frozen constant** | **does not fit as stated** (O8) |

**The frozen constant, now against bundled sources [r2].** `universalBlockBound c α =
3·|serialize| + 5·(n + 1) + 20` (`TuringMachine/UniversalBlock.lean:750`).
`timed_universal_concrete` (`TuringMachine/Universal.lean:2844`) displays the coefficient
`3|α| + canonizerTime(|α|) + |serialize| + 2·|bits(n)| + 2·q₀ + 16 + universalBlockBound + 14`,
and TMSAT's public bridge `timed_universal_quantitative` (`ClassNP/TMSAT.lean:710`) bounds it
by `3|α| + 14·canonizerTime(|α|) + 50` through the private arithmetic lemma
`tmsat_concrete_coefficient` (`:670`). The block's stated per-round `50·(|table| + 1)` exceeds
`universalBlockBound`. As the auditor notes, a larger *available* upper bound does not show that
the *actual* time exceeds the old bound; the obligation is open. U-1 chooses among sharpening the
block's time clause (a sibling theorem), restating the displayed coefficient (a statement gate
and TMSAT's re-check), or keeping the chapter-1 timed layer, and none of these is pre-approved:
each revises U-1's recorded requirement. Not a promotion blocker.

### 2.6 Summary

| Consumer | Verdict for the step block | What else it waits on |
|---|---|---|
| H1 | as is (consumed in fills-8) | startup, canonizer installation, the joint ledger |
| EXPCOM | as is (through H1) | H1 |
| B6 `U₀` / `SU` | as is, plus `roundTM_visited`, the cofinal `roundTM_iterate`, CO-RF | H3, H5 (ruler, block simulation), `U₀`'s fill |
| C1 | as is (lifted-table identity), plus a choice installer | SC-3, H5 |
| U-1 | as is, except the frozen constant (O8) | H5 (time, cofinality), CO-RF, the O8 decision |

None of the consumers needs a copied contract changed.

---

## 3. Recommendation

### 3.1 Promote as is now, and generalize later

Unchanged from round 1: no named consumer needs a block change (§2.6), the move costs no proof
work (now rehearsed at the integration base, §4.6), it unblocks the host-first rule
(`workflow.md:133`), and MIG-0b's round layer would force a second migration of any
generalization made now.

### 3.2 The alternative: generalize at promotion

Unchanged (round-1 §3.2): an output mode (superseded by CO-RF's wrapper), a choice-indexed lookup
(superseded by the lifted-table identity) and a sharper time clause (the only real candidate, as
a later sibling theorem).

### 3.3 The `Contract` phrasing, and how it migrates [r2]

* **MIG-0a has landed.** `Turing.Contract` (`Build/Contract.lean:143`) is a first-exit contract
  whose cut includes time 0; `ReturnContract` (`:783`) has a single, positive return. The round
  fits neither: `entry` is both the start and an exit, and there is a distinct escape `halt`
  (the module's own docstring says so: "a round that may instead end at a distinct escape ...
  belongs to MIG-0b's round layer").
* **MIG-0b's draft round layer is exactly the round's shape.** `RoundContract`
  (`audits/evidence/mig0b/Contract-mig0b-draft.lean.txt:1636`): positive exact time, an interior
  live and off the anchor and the escapes, an endpoint at the anchor or an escape, a head
  envelope; `Round.iterate` (`:1620`) composes rounds into segments.
* **The adapter, with no re-proof**, when MIG-0b lands:
  `roundTM_round : RoundContract (roundTM k) ⟨.entry, ()⟩ {some ⟨.halt, ()⟩} ι x`, with `pre :=
  Rep ∧ live`, `time :=` the first positive exit (well defined by `Nat.find`, and equal to every
  witness of `roundTM_effect` by `roundTM_firstExit_unique`), `post := runFrom`, envelope
  intervals `[min, max]` of the start and end positions for the bank and input, `[-B, B]` for the
  auxiliary heads. The existing-style theorem stays as its proof source.

---

## 4. The proposed public module

### 4.1 Home, name, namespace and imports

Unchanged: **`TCSlib/Complexity/TuringMachine/Build/StepBlock.lean`**, namespace
**`Turing.StepBlock`**; `workReadsK`/`tableBitsK` keep their `Turing.` names; the four generic
lemmas go to `Turing.MultiTapeTM`. **Imports: `CodeFormat`, `Build.Seam`, `Build.Catalog`.**
**[r2] Evidence:** the forward closure of these three imports (18 library modules) contains
neither `CodeSimulator` nor `CounterLoop` nor `VirtualInput`, and the move's code references no
staying `CodeSimulator` declaration (MEASURED: `importclosure.out` §5; `movemanifest.out`,
*Layering*). The generated module elaborates under exactly these imports (§4.6).

### 4.2 What moves, and the round-2 surface [r2] (O5)

121 declarations move (Appendix A): the layout pair, the five summary declarations and the 114
step-block declarations. Six are added (the additive results). **The surface is narrowed without
changing any contract**, by one rule: *a moved declaration is public iff it occurs in a public
statement, in the carrier types of the public state type `Σ key, Ph k key` (closed under their
bodies), or in a body a consumer unfolds to establish or read the contract (`Rep`, `exit`,
`summaryCells`, `tableTape`, `summaryTape`)*. `movemanifest.out` (*Surface*) checks the rule
mechanically: no public statement or unfolded body names a proposed-private declaration, and
the six additive statements name none.

| Tier | Visibility | Members |
|---|---|---|
| A, consumer interface | public | `workReadsK`, `tableBitsK`, the five summary declarations, `tableTape`, `summaryTape`, `summaryCells` and its four layout lemmas, `Key`, `Ph`, `SeekCtrl`, `SeekKey`, `SeekPh` (carrier types of the state type), `exit`, `roundTM`, `roundFinTM`, the four instances on `Ph` and `SeekPh`, `Rep`, `roundTM_effect`, `mem_workReadsK`, `length_workReadsK`, the two generic `MultiTapeTM` run lemmas |
| B, component contracts | public | `recordWidth`, `RecordState`, `recordTM`, `recordFinTM`, `recordTM_effect`; `SuccPhase`, `succFieldTM`, `succFieldCfg`, `afterTag`, `succFieldTM_run`/`_cut`/`_heads`; `SkipPh`, `recordSkipTM`, `recordSkipTM_run`/`_spec`, the two `SkipPh` instances |
| **C, implementation helpers (round 1: public)** | **private** | `payload`, `applyPayload`, `workRank`, `inputRank`, `readRank`, `skipPart`, `skipRed`, `seekRouterTM`, `seekNext`, `seekPart`, `seekRed`, `seekTM`, `twoMoveTM`, `part`, `red` |
| D, trace internals | private (both rounds) | the other 56 |

Counts (MEASURED, `movemanifest.out`): round 1, 65 moved public = 41 definitions/types + 6
instances + 18 theorems (with the 5 additives, the auditor's 70 = 41 + 6 + 23); **round 2, 50
moved public = 26 definitions/types + 6 instances + 18 theorems, 56 with the 6 additives**.
Tier C names occur only in the bodies of the public machines `recordTM` (`payload`,
`applyPayload`), `recordSkipTM` (`skipPart`, `skipRed`) and `roundTM` (`part`, `red`, and through
them `seekTM`, `seekRouterTM`, `seekNext`, `seekPart`, `seekRed`, `twoMoveTM` and the ranks),
which consumers do not unfold; a later sibling theorem
that needs them (O8's sharper clause) lives in `StepBlock.lean` itself. The carrier types stay
public because they occur in the state type that every public statement names; an opaque state
type was the other option and would change statement text (round-1 O5). **Gate rule:** if the
manifest at the H2-M base reports a staying reference to a tier-C name (it reports none at
1781a230), that name stays public with an "implementation detail" docstring sentence instead.

### 4.3 What changes in `CodeSimulator.lean`: the declaration-based manifest [r2] (finding 5)

Computed by name at 1781a230 by `movemanifest.py` (`movemanifest.out`); nothing depends on line
numbers, and the maintainer reruns it unchanged on any later base before H2-M.

1. **Imports.** Add `import TCSlib.Complexity.TuringMachine.Build.StepBlock`; the six existing
   imports stay (the canonizer and H1's clock use them).
2. **Deletions, by name:** the 121 declarations of Appendix A (with their docstrings) and the
   comments between them. **No private copy is kept.** The section comment `/-! ### Finite output
   summary` (`:2764`) stays with the summary clock; its sentence "The seven output-summary and
   clock declarations below" becomes status text to correct (four clock declarations remain;
   the five summary declarations moved).
3. **The clients section.** After the deletions the summary-clock family (`summaryClock`,
   `_correct`, `_accepts`, `_zero`; `:2814–2851`) and H1's clock (11 declarations, `:5752–6132`)
   are adjacent. **They are wrapped in one `section StepBlockClients` with `open StepBlock`**:
   - the family's text is unchanged; `outputSummary`, `summaryEmit`, `outputSummary_append`,
     `outputSummary_true` resolve to `Turing.StepBlock.*`; no other library declaration has
     these names, and the rehearsal elaborates without ambiguity;
   - H1's 11 declarations have their references renamed by the rename map (`h1RoundTM` →
     `roundTM`, `h1RoundExit` → `exit`, `h1RoundPh` → `Ph`, `h1RoundRep` → `Rep`,
     `h1Round_effect` → `roundTM_effect`, `h1SummaryTape` → `summaryTape`, `h1SummaryState` →
     `summaryCells`; 35 references in all, listed in `movemanifest.out`). Every renamed name is
     tier A, so public. Their own names (`h1ClockTM`, ...) stay. Their statements change only by
     this injective renaming of constants.
   - The manifest fails if any other staying declaration uses a moved name outside the layout
     pair (none at 1781a230), or if a declaration other than these 15 falls inside the section.
4. **Layout users** (`serializeK`, `workReadsK_one`, `workReadsK_two`, `tableBitsK_two`,
   `oneTape_serialize_eq`, and H1's clock): unchanged, since `Turing.workReadsK`/`tableBitsK`
   keep their names.
5. **Status text** (comments and docstrings outside the moved code naming moved declarations):
   the module status bullet (`:53`, `:57`) and the headline's fill appendices (`:6171–6203`)
   switch to the public names; H1's clock docstrings are renamed with item 3.
6. **No other library file** names a moved declaration (only the public layout pair could be
   named, and none is).

**Single-file rehearsal.** `PostMoveProbe.lean` is the generated `StepBlock` module followed by
`CodeSimulator.lean` with exactly these edits (items 2–3): 0 errors, the two headline sorries,
**0 other warnings** (MEASURED, `elaboration.log`). Being one file, it cannot test cross-module
privacy; the manifest's reference check does that (every reference from staying code is to a
public name).

**Timing (O2).** Fills-8 integrated both B5a continuations, so the round-1 ruling applies: H2-M
lands in a coordinated window **before the next B5a continuation is briefed**, never beneath an
active H1 worker; a canonizer continuation may run concurrently only under a declaration
carve-out disjoint from the 121, the clients section, the imports and the status text above.

### 4.4 The maintainer's PR, in three commits [r2]

1. **The move, with the freeze check.** Create `Build/StepBlock.lean` from the declarations
   generated by name (`movemanifest.py --visibility proposed --h2m-edits`), with the public
   docstrings of the draft; make the `CodeSimulator.lean` edits of §4.3; update the facade.
   **The H2-M text edits of §4.7 belong here**, so that the new module lands with every line
   within 100 Unicode characters (finding 8's landing criterion) and no linter warning.
   Check: `movemanifest.py --compare-to Build/StepBlock.lean` against the H2-M base, which
   compares all 121 bodies modulo the rename map, comments, whitespace and visibility (and the
   one binder name).
2. **The additive results** (six), with the draft's proofs.
3. **Style.** Nothing is left: H1's fills-8 cleanup removed 66 of the 67 inherited warnings, and
   the edits of commit 1 remove the last one and the remaining over-width lines (MEASURED:
   `MovePlusAdditive-r2` elaborates with 0 warnings; the edited move has no line over 100
   characters, `linelen.out`). Commit 3 is dropped unless the replay shows otherwise.

### 4.5 The replay closure [r2] (MEASURED, `importclosure.out`)

`importclosure.py` reads only the header `import` lines of the 625 library modules (1,624
internal edges, no dangling import). The reverse closure of `CodeSimulator` is 6 modules:
`Codes2Tape`, `Diagonalization.EXPCOM`, `Diagonalization.Relativization`, the facades
`TuringMachine` and `Diagonalization`, and the root. With the proposed edges overlaid
(`StepBlock` importing its three modules; `CodeSimulator` and the facade importing
`StepBlock`), the reverse closure of `StepBlock` is those 6 plus `CodeSimulator`: **the replay
set is 8 modules** (the script asserts it). No Lean file outside the lake library imports
`CodeSimulator`. The alternatives: home `CodeFormat` (O3), 23 reverse dependencies, a 24-module
replay; home `Deterministic` (O9), 223, a 224-module replay. The full graph is
`import-graph.txt`.

### 4.6 The gates, and what has and has not been checked [r2] (finding 3)

**Checked in this round (probes; none is the H2-M replay):**

| Check | What it shows | What it does not show |
|---|---|---|
| Round-1 move probe (`MoveProbe.lean.txt`) | the 121 declarations elaborate under the three imports (at fills-7) | stale for 24 bodies since fills-8 |
| Round-2 name-based regeneration vs round 1 | the code of exactly the 24 cleaned-up declarations changed; no statement or definition did | — |
| `MovePlusAdditive-r2.lean` | the move generated at 1781a230, with the proposed visibility and the H2-M edits, plus the six additives: 0 errors, 0 sorries, 0 warnings; all 127 axiom prints within `{propext, Classical.choice, Quot.sound}` | cross-module visibility; downstream modules |
| `PostMoveProbe.lean` | `CodeSimulator.lean` after commit 1, in one file with the module: 0 errors, the 2 headline sorries, 0 warnings | private-name access across modules (covered by the manifest); the facade; downstream modules |
| `AlphaProbe`, `AlphaNeg` | the H2-M text edits are α-equivalent (§4.7) | — |

**Still to come, at H2-M:** the PR's own replay of the 8-module closure with fresh `.olean`s, the
two files as separate modules (so privacy is enforced), sorry sets unchanged (`CodeSimulator` 2,
`StepBlock` 0, the others as before); the freeze check of commit 1; axiom prints of every new
public declaration; the lint at 0 FAIL; a duplication screen showing no copy left in
`CodeSimulator`. Then the H2-M gate (freeze, replay, fidelity), and the records: registry row H2
"public, gated" (`machine-library-design.md:3063`), F7-1(a) closed (`backlog.md:553`), the next
H1 brief citing `Turing.StepBlock.*`.

### 4.7 The H2-M text edits: the H1 escalation [r2]

H1's continuation 2 left 14 over-width lines in frozen signatures and definition bodies and the
unused binder `hr` in the statement of `h1Seek_stateStep` (`:4040`), and escalated them rather
than edit frozen text (`h1-3-escalation-excerpt.md`; fills-8 record, *Disposition*). The move
re-homes these declarations anyway, so it is the natural place. **Proposal: re-wrap every line
that exceeds 100 characters after renaming, by whitespace only, and rename the binder `hr` to
`_hr`. Neither changes any statement or definition, up to α-equivalence.**

**The lines** (MEASURED, `linelen.out` and `movemanifest.out`, *Width*). Renaming alone changes
the set:
- of H1's 14, six fall within 100 characters by renaming (`h1SeekRed`, `h1Seek_request`,
  `h1RoundRed`, `h1RoundPh_decidable`, `h1Round_phase`; `h1Round_effect`'s line becomes exactly
  100); eight remain;
- renaming lengthens six other lines past 100 (`h1Data` → `roundData`, `h1Run_input` →
  `MultiTapeTM.inputPos_runFrom_of_inputTape_eq_zero`): one declaration header and five proof
  lines.

So the unedited move has 14 over-width lines, in 10 declarations: in statements or definition
bodies, `seekRouterTM` (definition), `tableBitsK_cut`,
`MultiTapeTM.inputPos_runFrom_of_inputTape_eq_zero` (binder line), `Ph` (definition),
`roundData_window`, `roundTM_payload` (2), `roundTM_canonical` (1), `rep_entry`; in proof bodies,
`roundTM_prepare` (2), `roundTM_restore` (1), `roundTM_canonical` (2). The edit table
`H2M_EDITS` of `movemanifest.py` re-wraps each, breaking only inside brackets or before an
argument indented past its application's column (the layout rules that bind statements and
tactic blocks). With the edits, **no line of the module exceeds 100 characters** (longest 100).

**Why nothing changes.**
- *Re-wrapping* leaves the token sequence unchanged: the manifest checks that every edited
  declaration is token-identical to the unedited one (comments and whitespace ignored). Equal
  tokens under the same layout parse to the same syntax, hence elaborate to the same term; a
  break in a layout-sensitive position would be a parse error, not a different term, and the
  module elaborates without errors or warnings.
- *`hr` → `_hr`* renames a λ-binder inside `dite (rank.val = 0) (fun hr => .done) (fun hr => ...)`
  in the statement: the elaborated statement is the same up to binder names, i.e.
  α-equivalent. *Dropping* the binder instead would produce the non-dependent `ite`, a
  different constant: definitionally equal only after unfolding `ite`, propositionally by
  `dite_eq_ite`, and its two uses (in `seekTM_rank` and `seekTM_groups`, `:4086`, `:4199`)
  would need proof edits. **Recommend
  `_hr`; reject dropping.**
- **Mechanical check** (`AlphaProbe.lean`, MEASURED): for each of the 11 edited declarations
  the probe declares its unedited copy `X_orig` and proves `type_of% @X_orig = type_of% @X` by
  `with_reducible rfl`, which unfolds nothing but reducible constants (so it holds for
  α-equivalent statements, embedded proofs being irrelevant), and for the two definitions also
  `@X_orig = @X` by `rfl`: **0 errors**. **Negative control** (`AlphaNeg.lean`): the
  dropped-binder statement fails the same check (one error, `rfl` failed).

Of the 11 edited declarations, nine are private in round 2 (`seekRouterTM`, public in round 1,
becomes private under O5) and two are public with whitespace-only changes (`Ph` and the generic
run lemma). The round-2 draft already shows `seekRouterTM` and `Ph` in exactly this wrapped
form, and the fidelity check passes on it.

---

## 5. Open questions [r2]

* **O1. Name collision.** Resolved: the backlog item is now "B5a linear headline"
  (`backlog.md:1396`).
* **O2. Timing.** §4.3, *Timing*: a coordinated window after fills-8, before the next B5a brief.
* **O3. Home of `workReadsK`/`tableBitsK`.** StepBlock now (8-module replay); `CodeFormat` at a
  later shared-file window (24-module replay). Counts now MEASURED (§4.5).
* **O4. Three summary encodings.** Unchanged: promote the cell code; maintainer-owned dedup with
  a bridge to `OutSummary`. (The B6 hosts land `outSummaryCode`/`summaryTag` in `ConfigGraph`,
  `machine-library-design.md:3886`, which joins the same family.)
* **O5. Public surface.** Ruled in §4.2: 15 helpers private, 56 public names.
* **O6. The additives.** Included, six, with finding 1's repair.
* **O7. A round-time function.** **[r2]** H1 now has one, privately (`h1RoundTime`,
  `h1RoundTime_spec`). Recommendation: keep them in `CodeSimulator` at H2-M (the inventory stays
  121, no new statement at this gate); record a maintainer-owned dedup item to replace them by a
  public `StepBlock.roundTime` with MIG-0b's adapter, whose `time` is the same function. The
  small duplicated argument (the `least` step against `roundTM_firstExit_unique`, about a dozen
  lines, ESTIMATE) is disclosed here for the ledger.
* **O8. U-1's frozen constant.** Unresolved, recorded on U-1 (§2.5); no choice pre-approved.
* **O9. Home of the run head bound.** StepBlock now; `Deterministic` with MIG-1 (224-module
  replay).
* **O10. Style debt.** Absorbed: §4.4 commit 1 and §4.7.
* **O11. A requirement on H5.** **[r2] Revised (§2.3a):** a positive, finite block simulation;
  literal lockstep only for Z1 and the native device; per-consumer resource guarantees.
* **O12. F7-1(c), the fixed-field walk.** **[r2] Qualified as the auditor ruled.** Exporting
  `recordTM`/`recordTM_effect` does not resolve F7-1(c): it assumes canonical bits and executes
  the payload. The fixed-prefix walk's framed read contract is the private `recordTM_read`
  (`h1Record_read`, `:2978`: any prefix of fixed bits, no canonicity premise). It stays private
  at H2-M; if the canonizer's validator needs it, it is promoted by its own statement gate. The
  factoring obligation stays open on F7-1(c).
* **O13 [r2]. CO-RF** (§2.3b): recorded on `U₀`'s sketch and U-1's entry at H2-M.
* **O14 [r2]. H5 gate items** (§2.3a): cofinality on `exists_rulerHostTM`; the stale
  "binary-position" mentions.

---

## 6. Size and splitting [r2] (finding 7)

**Sizes** (reported, not acted on). The generated module with the H2-M edits is 2,986 lines
(MEASURED, `MoveProbe-r2.lean`), the additive results about 290 (MEASURED in
`MovePlusAdditive-r2.lean`), and the public docstrings and module header add about 250
(ESTIMATE): **about 3,500 lines (ESTIMATE)**. `CodeSimulator.lean` falls from 6,230 to about
3,260 (MEASURED in the rehearsal).

**The size rule.** `policy.md` §1 asks for a split of a file approaching 1,000 lines "unless
there is a positive reason not to". The user's standing rule (2026-10-11) makes that guidance
advisory for this campaign: a large file is not a problem in itself; splits are made only for a
positive reason such as layering or reuse, never for size alone. So the question is whether a
Record / Seek / Round split has a layering or consumer reason. It has none, and it has a
concrete cost:

- **Consumers.** Every named consumer (H1, EXPCOM through H1, `U₀`, `SU`, C1, U-1) uses the
  round. None imports the record reader or the skipper alone. The one candidate, F7-1(c)'s
  canonizer, lives in `CodeSimulator`, which imports `StepBlock` in any case, and its need is a
  read contract (O12), not a separate module.
- **Layering.** The three parts have the same imports; Seek uses Record, Round uses both. A
  split gives a chain whose lower links no one imports alone, and the same 8-module replay.
- **Cost** (MEASURED, `splitcost.out`): the parts would be 573, 1,151 and 950 lines of code,
  and **19 declarations that round 2 keeps private** (tiers C and D: the reader's frame
  `readCfg`, the trace lemmas `recordTM_read`/`_execute`, the ranks, `seekTM`, `seekCfg`,
  `seekTM_select`, `twoMoveTM`/`_run`, ...) are used across the cuts. A split would have to
  publish them, or copy them, against O5 and the duplication rule.

**Ruling: one module now. Resolution point:** revisit if a consumer needs the record reader or
the skipper without the round (for instance a promoted fixed-prefix read contract for F7-1(c)
whose consumer is not `CodeSimulator`), or when MIG-0b's adapter or O8's sibling time clause
adds a layer that some consumer imports without the round.

---

## 7. Evidence [r2]

All in `h2/r2/` unless noted; regenerated end to end by `run-all.sh` (`python3 -I` only; Lean
only through the read-only `leanelab.sh`).

* **`StepBlockDraft-r2.lean.txt`**: 1,039 lines, 64 declarations (58 copied + 6 additive).
  **0 errors, 7 `sorry` warnings (the seven contracts), 0 other warnings** (`elaboration.log`).
  All lines within 100 Unicode characters (longest 96; the metric is Unicode characters,
  `linelen.out`). The repository's style lint reports only the size line (`style-lint.out`).
* **Axiom probe** (a copy of the draft with 64 prints, `elaboration.log`): **54 declarations
  use at most `propext`, `Classical.choice`, `Quot.sound`; 10 also use `sorryAx`: the seven
  contracts, and `roundTM_visited`, `roundTM_iterate`, `roundTM_firstExit_unique`, which
  depend on the sorried main contract.** (Finding 8: round 1's unqualified "at most the standard
  three" overlooked the two corollaries with `sorryAx`.) Against the proved contract
  (`MovePlusAdditive-r2`), all 127 declarations print within the standard triple.
* **Fidelity** (`fidelity-r2.py.txt`; `fidelity-r2-pass.log`): **58 of 58** copied declarations
  match `CodeSimulator.lean` at 1781a230 after renaming; their code is byte-identical to the
  round-1 draft's (docstrings changed: `outputSummary`, a rewrap; `Key`; `roundTM_effect`); the
  additives are exactly the six whitelisted; no `sorry` outside the seven contracts. **Negative
  controls** (`fidelity-r2-negctl.log`): seven mutations (two content mutations as in round 1, a
  post-`let` statement mutation, a missing, an unexpected and a duplicate declaration, an
  admitted additive) each exit 1; the round-1 script exits 0 on three of them.
* **Manifests**: `importclosure.out` with `import-graph.txt` (§4.5); `movemanifest.out` (§§1.5,
  4.2, 4.3, 4.7); `movemanifest-vs-r1-strict.out`; `movemanifest-negctl.log` (a simulated next
  base: a new h1 lemma, a renamed and a tier-C reference in the headline, one changed proof;
  exit 1, four failing checks).
* **Probes**: `MovePlusAdditive-r2.lean.txt` with its output; `PostMove-CodeSimulator.lean.txt`
  (the rehearsed `CodeSimulator.lean` part) with its output; `AlphaProbe-tail.lean.txt`,
  `AlphaNeg-tail.lean.txt` and outputs; `ResetProbe-tail.lean.txt`. The probe files that begin
  with the generated module are reproduced from it by `mkprobes.py`/`mkalpha.py`.
* **Size**: `splitcost.py.txt`, `splitcost.out`; `linelen.py.txt`, `linelen.out`.

---

## Appendix A. The rename map, with the round-2 visibility

The names are as in round 1 (`audits/evidence/h2/H2-design.md`, Appendix A); the map is
injective and asserted so by `movemanifest.py`. Visibility in round 2: **A**/**B** public,
**C** private (round 1: public), **D** private.

| Original (`CodeSimulator.lean`) | Proposed | Tier |
|---|---|---|
| `workReadsK`, `tableBitsK` | unchanged (`Turing.`) | A |
| `outputSummary`, `summaryEmit`, `outputSummary_append`, `outputSummary_true`, `summaryEmit_other` | `StepBlock.` + same | A |
| `h1RecordWidth`, `h1RecordState` | `recordWidth`, `RecordState` | B |
| `h1TableTape`, `h1SummaryTape` | `tableTape`, `summaryTape` | A |
| `h1Mirror_ne_table`, `h1Summary_ne_table`, `h1Mirror_ne_summary` | `mirror_ne_table`, `summary_ne_table`, `mirror_ne_summary` | D |
| `h1Payload`, `h1ApplyPayload` | `payload`, `applyPayload` | **C** |
| `h1RecordTM`, `h1RecordFinTM`, `h1Record_effect` | `recordTM`, `recordFinTM`, `recordTM_effect` | B |
| `h1ReadCfg`, `h1Payload_correct`, `h1Record_read`, `h1Record_execute`, `h1Record_envelope` | `readCfg`, `payload_correct`, `recordTM_read`, `recordTM_execute`, `recordTM_envelope` | D |
| `h1WorkReads_mem`, `h1WorkReads_length` | `mem_workReadsK`, `length_workReadsK` | A |
| `h1WorkRank`, `h1InputRank`, `h1ReadRank` | `workRank`, `inputRank`, `readRank` | **C** |
| `h1SuccPhase`, `h1SuccTM`, `h1UnaryCfg`, `h1AfterTag` | `SuccPhase`, `succFieldTM`, `succFieldCfg`, `afterTag` | B |
| `h1Unary_step`, `h1Unary_run`, `h1Succ_trace` | `succFieldTM_unary_step`, `succFieldTM_unary_run`, `succFieldTM_trace` | D |
| `h1Succ_run`, `h1Succ_cut`, `h1Succ_heads` | `succFieldTM_run`, `_cut`, `_heads` | B |
| `h1SkipPh`, `h1SkipTM` | `SkipPh`, `recordSkipTM` | B |
| `h1SkipPart`, `h1SkipRed` | `skipPart`, `skipRed` | **C** |
| `h1Skip_fixed`, `h1Skip_tail`, `h1Action_split`, `h1Reads_append`, `h1Action_reads`, `h1Skip_path` | `recordSkipTM_fixed`, `recordSkipTM_tail`, `actionBitsK_split`, `reads_append`, `actionBitsK_reads`, `recordSkipTM_path` | D |
| `h1Skip_run`, `h1Skip_spec`, `h1SkipPh_finite`, `h1SkipPh_decidable` | `recordSkipTM_run`, `recordSkipTM_spec`, `instFintypeSkipPh`, `instDecidableEqSkipPh` | B |
| `h1SeekCtrl`, `h1SeekKey`, `h1SeekPh`, `h1SeekPh_finite`, `h1SeekPh_decidable` | `SeekCtrl`, `SeekKey`, `SeekPh`, `instFintypeSeekPh`, `instDecidableEqSeekPh` | A (carrier types) |
| `h1SeekRouter`, `h1SeekNext`, `h1SeekPart`, `h1SeekRed`, `h1SeekTM` | `seekRouterTM`, `seekNext`, `seekPart`, `seekRed`, `seekTM` | **C** |
| `h1SeekCfg`, `h1Seek_request`, `h1SeekCost`, `h1Seek_many`, `h1Seek_stateStep`, `h1Seek_rank`, `h1SeekShift`, `h1Seek_groups`, `h1Seek_observe`, `h1Seek_lookup`, `h1Seek_select` | `seekCfg`, `seekTM_request`, `seekCost`, `seekTM_many`, `seekTM_stateStep`, `seekTM_rank`, `seekShift`, `seekTM_groups`, `seekTM_observe`, `seekTM_lookup`, `seekTM_select` | D |
| `h1ReadActions`, `h1ReadActions_length`, `h1ReadActions_at`, `h1Table_groups`, `h1Table_cut`, `h1Records_length`, `h1Groups_length` | `readActions`, `readActions_length`, `readActions_at`, `tableBitsK_groups`, `tableBitsK_cut`, `records_length`, `groups_length` | D |
| `h1Run_headBound`, `h1Run_input` | `MultiTapeTM.abs_workTapePos_runFrom_sub_le`, `MultiTapeTM.inputPos_runFrom_of_inputTape_eq_zero` | A |
| `h1Unary_read`, `h1Buffer_outside`, `h1Buffer_reads`, `h1Buffer_suffix` | `bufferTape_unary`, `bufferTape_outside`, `bufferTape_reads`, `bufferTape_suffix` | D |
| `h1SummaryState`, `h1SummaryState_cell`, `_update`, `_copy`, `_clear` | `summaryCells`, `summaryCells_shift`, `_update`, `_copy`, `_clear` | A |
| `h1TwoMoveTM` / `h1TwoMove_run` | `twoMoveTM` / `twoMoveTM_run` | **C** / D |
| `h1RoundPh_finite`, `h1RoundPh_decidable`, `h1RoundKey`, `h1RoundPh`, `h1RoundExit`, `h1RoundTM`, `h1RoundFinTM` | `instFintypePh`, `instDecidableEqPh`, `Key`, `Ph`, `exit`, `roundTM`, `roundFinTM` | A |
| `h1RoundPart`, `h1RoundRed` | `part`, `red` | **C** |
| `h1Data`, `h1Data_shift`, `h1RoundWindow`, `h1Data_window`, `h1RoundSpan`, `h1RoundSpan_add`, `h1Round_phase`, `h1At`, `h1Window_frame`, `h1Data_stateCell` | `roundData`, `roundData_shift`, `RoundWindow`, `roundData_window`, `RoundSpan`, `RoundSpan.add`, `roundTM_phase`, `atKey`, `roundWindow_frame`, `roundData_stateCell` | D |
| `h1Round_prepare`, `h1Round_payload`, `h1Round_restore`, `h1Round_lookup`, `h1Round_canonical`, `h1RoundRep_entry` | `roundTM_prepare`, `roundTM_payload`, `roundTM_restore`, `roundTM_lookup`, `roundTM_canonical`, `rep_entry` | D |
| `h1RoundRep`, `h1Round_effect` | `Rep`, `roundTM_effect` | A |
| (new) | `summaryEmit_none`, `MultiTapeTM.visitedByTapeHead_add_subset`, `MultiTapeTM.visitedByTapeHead_step_subset`, `roundTM_visited`, `roundTM_iterate`, `roundTM_firstExit_unique` | additive, public |

## Appendix B. Commands (read-only)

```
S=<scratchpad>; WT=$S/wt-r2h2; OL=$S/oleans-f8; R=$S/r2-h2    # checkout at 1781a230
bash $R/run-all.sh                                           # everything below, with checks
python3 -I $R/importclosure.py $WT $R/logs/import-graph.txt
python3 -I $R/movemanifest.py $WT --visibility proposed --h2m-edits \
  --emit-move M.lean --emit-postmove P.lean \
  --compare-to $WT/audits/evidence/h2/MoveProbe.lean.txt --allow-body-diff <the 24 names> \
  --draft $R/StepBlockDraft-r2.lean --additive <the 6 names>
python3 -I $R/fidelity-r2.py $WT $R/StepBlockDraft-r2.lean \
  --r1 $WT/audits/evidence/h2/StepBlockDraft.lean.txt
bash $S/tools/leanelab.sh $WT $OL <absolute path of each probe>
# at H2-M, on its base and after the PR:
python3 -I movemanifest.py <base checkout> --compare-to <PR>/TCSlib/.../Build/StepBlock.lean \
  --additive <the 6 names>
```
