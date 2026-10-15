# B5a H1 continuation — partial delivery at a complete step block

**Headline target: 0/1. The complete generic step block is proved; `MachineFormat.exists_uniformSimulator` retains its original direct admission.** This is the rule-9 partial boundary explicitly permitted by `briefs/b5a-fill-h1-cont.md`. The inherited frontier's items 1–3 are complete. Items 4–6 remain. There are **98 new private declarations, none admitted**. No target is claimed proved modulo an unfinished new helper.

## Repository and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Exact starting branch: `complexity/arora-barak-ch3-4`; `main` was never checked out.
- Base: `9e34c048e9d527744eec87766b385bb1b2ff7a98`.
- Work branch: `fill/b5a-h1-cont`.
- Delivery commit: `df8aea136aa7d8cfad89b0c78f69869a52692fa4`.
- Required ancestor: `c0eefa8be8c277777dfecd8d2510d8e57218ce4c`. The required `git merge-base --is-ancestor` succeeded before editing (exit 0, `evidence/ancestor.log`). The issue ancestor-to-base change consists only of four Markdown files; no Lean change separates the issue's proof base from this base.
- No push, PR, rebase, or mutation of another branch. The only tracked change is `TCSlib/Complexity/TuringMachine/CodeSimulator.lean`.
- The entire new development is private in the owned gap after `h1Record_effect`. The sole other change is an additive **Fill appendix (H1 continuation, partial; complete generic step block)** before the target docstring's closing delimiter. The target's signature, original docstring text, pending tag, and original `sorry` body are unchanged.
- All **78 inherited private declarations**, the parallel canonizer's target and gap, all other declarations, imports, and the module header are byte-identical to the base. Removing the new gap and appendix reconstructs the complete base file exactly. No public declaration was added.
- Final source: **4207 lines, 13 public / 176 private declarations** (98 new privates). The size warning is justified by this brief's uncapped rule 8 and declaration ownership; moving code to a shared file is the maintainer's integration task.

The frozen module header now understates the result: its “rest of the step block (record lookup, successor installation, restoring the round seam)” remains listed as open. The maintainer should update that text at integration. It was deliberately left untouched. The headline H1 pending status remains accurate.

## What is complete

`h1RoundFinTM k` is one finite binary machine with `k + 2` work tapes, and no parameter for the coded state count. Source state is unary data. The first `k` tapes mirror source work tapes; auxiliary tape `k` contains the immutable `tableBitsK` word; auxiliary tape `k + 1` contains the summary at cell 0, a blank at cell 1, and the unary source state beginning at cell 2. Both auxiliary heads are at home 0 at the seam. Sharing the state word with the summary tape is a deliberate choice within the brief's nonbinding recommendation of a separate state tape.

The selector captures the source input/work read rank in the exact serializer order (input blank/false/true; tape 0 outermost in `workReadsK`). It skips `q` groups of `3^(k+1)` **whole variable-width records** and then the read-rank suffix. `h1SkipTM` reuses `h1RecordTM` only up to the fixed-width boundary, dispatching before execution. A shared successor leaf walks the variable state field, either without copying during lookup or copying during installation. It performs no validation and is not a canonizer or grammar parser.

After selection, landed `skipTM`, `skipBackTM`, and `clearTM` contracts restore and clear the old state word. The inherited `h1Record_effect` applies every source action field and updates `summaryEmit`. The successor leaf installs the next unary state (or an empty word for simulated halt). Catalog scans return the table and state heads home. A simulated halt reaches a **live** `.halt` control only after its writes, moves, emission summary, and restoration are complete. A live successor returns to `.entry`. The strict interior visits neither exit.

The proof gives `0 < T ≤ 50 * (|table| + 1)`, including every dispatch and delimiter move. Thus the coefficient is independent even of `k`, and in particular independent of the state count, input, and simulated time. At every physical prefix, each mirrored/input head is at its start or action endpoint, at distance at most one. Every auxiliary head is within the same linear bound of its start and returns to zero. Physical output is unchanged at **every** prefix, for an arbitrary pre-existing physical output prefix. No simulator space ledger was attempted.

Hosting uses `phaseHostTM_run` and public state transport; the stationary entry dispatch uses `step_of_inputMoveAction`. There is no private replacement host or alternate run algebra. The input read is captured at lookup and the actual move occurs in the inherited payload, so the addendum's optional single input-device substep has not been imposed.

## Promotion candidate: host H2, step block; `machine-library-design.md` §14

Promote the machine, representation, exit convention, and the following **verbatim full contract** together. Control carriers are the finite `h1RoundKey`/`h1RoundPh k` family in the delivered source; they depend only on `k`. The representation and exit definitions are reproduced here so the endpoint and head clauses are unambiguous.

```lean
private def h1RoundExit (k : ℕ) (live : Bool) : Σ key, h1RoundPh k key :=
  if live then ⟨.entry, ()⟩ else ⟨.halt, ()⟩

private def h1RoundTM (k : ℕ) : MultiTapeTM (k + 2) Bool (Σ key, h1RoundPh k key) :=
  phaseHostTM (h1RoundPart k) ⟨.entry, ()⟩ (h1RoundRed k)

private def h1RoundFinTM (k : ℕ) : FinTM Bool where
  k := k + 2
  State := Σ key, h1RoundPh k key
  tm := h1RoundTM k

private def h1SummaryState (summary : Option Bool) (word : List Bool) (z : ℤ) : Option Bool :=
  if z = 0 then summary else FinTM.bufferTape word (z - 2)

private def h1RoundRep {k n : ℕ} {x : List Bool}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (c : Cfg k Bool (Fin (n + 1)) x)
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x) : Prop :=
  d.inputPos = c.inputPos ∧
  (∀ i : Fin k, d.workTapes (Fin.castAdd 2 i) = c.workTapes i ∧
    d.workTapePos (Fin.castAdd 2 i) = c.workTapePos i) ∧
  d.workTapes (h1TableTape k) = FinTM.bufferTape (tableBitsK tr) ∧
  d.workTapes (h1SummaryTape k) =
    h1SummaryState (outputSummary c.output) ((c.state.map unaryFin).getD []) ∧
  d.workTapePos (h1TableTape k) = 0 ∧ d.workTapePos (h1SummaryTape k) = 0
```

```lean
private theorem h1Round_effect {k n : ℕ} {x : List Bool}
    (tr : Fin (n + 1) → Option Bool → (Fin k → Option Bool) → Action k Bool (Fin (n + 1)))
    (c : Cfg k Bool (Fin (n + 1)) x) (q : Fin (n + 1)) (hq : c.state = some q)
    (d : Cfg (k + 2) Bool (Σ key, h1RoundPh k key) x)
    (entry : d.state = some ⟨.entry, ()⟩) (rel : h1RoundRep tr c d) :
    let a := tr q c.inputSymbol c.workTapeSymbols
    ∃ T, 0 < T ∧ T ≤ 50 * ((tableBitsK tr).length + 1) ∧
      let e := (h1RoundTM k).runFrom d T
      e.state = some (h1RoundExit k a.state.isSome) ∧ h1RoundRep tr (a.apply c) e ∧
      e.workTapeSymbols (h1SummaryTape k) = summaryEmit (d.workTapeSymbols (h1SummaryTape k)) a.output ∧
      (∀ u, 0 < u → u < T → ∃ s, ((h1RoundTM k).runFrom d u).state = some s ∧
        s ≠ ⟨.entry, ()⟩ ∧ s ≠ ⟨.halt, ()⟩) ∧
      (∀ u ≤ T, ((h1RoundTM k).runFrom d u).output = d.output) ∧
      (∀ u ≤ T,
        let f := (h1RoundTM k).runFrom d u
        (f.inputPos = d.inputPos ∨ f.inputPos = e.inputPos) ∧
        |(f.inputPos.val : ℤ) - d.inputPos.val| ≤ 1 ∧
        (∀ i : Fin k, f.workTapePos (Fin.castAdd 2 i) = d.workTapePos (Fin.castAdd 2 i) ∨
          f.workTapePos (Fin.castAdd 2 i) = e.workTapePos (Fin.castAdd 2 i)) ∧
        ∀ j : Fin (k + 2), |f.workTapePos j - d.workTapePos j| ≤
          if j.val < k then 1 else (50 * ((tableBitsK tr).length + 1) : ℕ)) ∧
      ∀ j : Fin (k + 2), k ≤ j.val → d.workTapePos j = 0 ∧ e.workTapePos j = 0
```

The full proof is in the accompanying source and its production-module axiom walk is in `axioms.log`. It has no `sorryAx` dependency, including no dependency on the canonizer or any other out-of-scope admission.

Additional promotion candidates:

- **Whole-record skipper:** `h1SkipTM`, `h1Skip_run`, `h1Skip_spec` (host H2, record skipper; §14). It is generic in `k`, independent of the coded state count, consumes the complete fixed and variable fields, never applies the skipped payload, and has exact cost `|actionBitsK a| + 1` including dispatch. Its leaf `h1SuccTM` and its framed/cut/head contracts are shared with successor installation.
- **Run head bound:** `h1Run_headBound`, the run form of public `workTapePos_step_le`, proved by a telescoping sum and the triangle inequality. This is a general shared lemma candidate.
- Small table-read/rank and buffer indexing identities may accompany the step block at promotion; they introduce no new encoding.

Requested blocking shared contract: **none**. Statement-freeze escalation: **none**. No claim is made that the unattempted startup/host/clock assembly is already discharged. The next batch must escalate any actual public-contract obstruction instead of changing a statement.

## Every new declaration and its role

Every declaration below is private and proved/defined without an admission. Derived finite/equality instances belong to the corresponding private state type.

| Declaration | Role |
|---|---|
| `h1WorkReads_mem` | Every vector of work reads occurs in the serializer's fixed enumeration. The proof follows its tape-zero-first recursion, independently of coded states. |
| `h1WorkReads_length` | There are exactly three possible reads on each mirrored tape. |
| `h1WorkRank` | Work-read rank is the index in the actual serializer order. |
| `h1InputRank` | Input symbols use the same blank/false/true order as the table writer. |
| `h1ReadRank` | The read-vector rank within a state block. Its bound depends only on `k`, so a physical controller may retain it in finite control. |
| `h1SuccPhase` | States of the trusted successor-field walker. The halt tag and the unary successor terminator lead to distinct live exits. |
| `h1SuccTM` | Walk an already canonized successor field. When `copy` is true, copy its unary state word to `dst`; when false, only advance the table head. No catalog leaf walks a bit-terminated, non-blank-delimited word. This leaf supplies that missing operation; it does not validate the grammar. |
| `h1UnaryCfg` | A framed prefix of the successor copy: the table head advances, and only an enabled destination receives the consumed prefix. |
| `h1Unary_step` | One unary-field transition writes precisely the next copied cell. The public prefix-write identity handles the destination's arbitrary frame. |
| `h1Unary_run` | Every prefix of a trusted unary state field has its literal physical trace, including the terminating false bit. The native input and output are fixed, and every unrelated head is fixed. |
| `h1AfterTag` | Configuration after the successor tag has been consumed. It is a one-cell table move and changes no other head, cell, input or output. |
| `h1Succ_trace` | The trusted successor walker consumes its entire variable-width field, optionally installing the unary successor in a blank destination. Its exit is live in both cases: `done false` means simulated halt, `done true` means a next state. This is a record leaf, not a grammar validator. |
| `h1Succ_run` | Endpoint of the successor-field trace, at exactly the field's bit length. |
| `h1Succ_cut` | Neither successor exit is visited before the field has been consumed. |
| `h1Succ_heads` | During a successor walk only the table head and an enabled destination head advance. Every input position and the physical output prefix are fixed. The exact formulas include both the halt tag and the last unary bit. |
| `h1SkipPh` | Phase family for a complete record skip. The fixed reader is stopped before its payload step; the successor walker then consumes the variable tail. |
| `h1SkipPart` | The skipper reuses the inherited fixed reader and the trusted tail leaf. |
| `h1SkipRed` | Dispatch at the fixed-width boundary, without executing the action. |
| `h1SkipTM` | One whole-record skipper, including its variable successor field. **Promotion candidate (host H2, record skipper; machine-library-design.md §14).** Its one stationary dispatch step is explicit in the cost. |
| `h1Skip_fixed` | The public phase-host theorem transfers the inherited prefix trace and then takes its sole dispatch. The payload transition is never executed. |
| `h1Skip_tail` | Once dispatched, the host follows the successor walker literally. This is an application of public state transport, not another host trace. |
| `h1Action_split` | A trusted action record splits at exactly the inherited fixed width. Only this elementary serialization identity is missing from the public reader's lower-bound contract; it also fixes the skipper's exact cost. |
| `h1Reads_append` | Split a literal, undelimited word read at an arbitrary physical origin. This small indexing fact is shared by fixed fields, record lists and state groups. |
| `h1Action_reads` | Expose the fixed and variable reads of one trusted record at an arbitrary physical table position. The tape outside the record is unrestricted. |
| `h1Skip_run` | A complete record is skipped silently. The exact elapsed time is its bit length plus the single phase dispatch. All tape cells are framed, and only the table head changes; the successor is not copied in skipping mode. |
| `h1Skip_path` | Every prefix of a whole-record skip preserves the complete data frame. At the sole dispatch the table head pauses; on every other transition it advances one cell. Neither successor exit can occur before the full field. |
| `h1Skip_spec` | The whole-record skipper's composition contract: a first live exit, complete framing, exact head trace, and a linear cost in the whole record. Both the prefix width and the finite controller depend on `k` alone. |
| `h1SkipPh_finite` | Each skipper phase is finite, uniformly in the coded state count. |
| `h1SkipPh_decidable` | Equality of the two skipper phase carriers is decidable. |
| `h1SeekCtrl` | The selector's finite router retains the current read rank and a within-group record countdown. The coded state itself stays on tape. |
| `h1SeekRouter` | Selector routing. The unary state begins at cell two of the summary auxiliary tape: cell zero is the summary and cell one its blank separator. Observation and one additional move enter that state word; each true skips one whole state block, and its false terminator selects the read rank. |
| `h1SeekNext` | The continuation after one skipped record. `rest` counts records still to skip after the current one, and `last` distinguishes the rank suffix from an entire state group. |
| `h1SeekKey` | Phase keys for the selector. `none` is its router; each finite countdown key tags a call of the same one-record skipper. |
| `h1SeekPh` | Finite state carriers of the selector's public phase host. |
| `h1SeekPart` | Selector phase machines: one router and the shared record skipper. |
| `h1SeekRed` | Only a requested call or a completed whole record dispatches. |
| `h1SeekTM` | The selector is one finite physical machine, independent of the number of coded states. The only loop is through the public phase host and the proved whole-record skipper. |
| `h1SeekCfg` | Reuse the reader's framed configuration as the selector's data, with only the finite router control renamed. |
| `h1Seek_request` | One requested whole-record call, with its two public-host dispatches. No intermediate point has the selector's final control. All data are framed, and every non-table head stays fixed throughout this call. |
| `h1SeekCost` | Cost of skipping a sequence of whole records through the selector: one skipper dispatch and two selector dispatches per record. |
| `h1Seek_many` | A finite within-group countdown traverses exactly its list of whole records. The table contents and the entire non-table data frame are preserved, and the final router control is first reached only after the last record. |
| `h1Seek_stateStep` | A unary-state router step either requests one complete state group and advances the state head, or requests the finite read-rank suffix. |
| `h1Seek_rank` | At the unary terminator, the selector skips exactly the read rank. This includes rank zero: the router's single silent step exits immediately. |
| `h1SeekShift` | The two auxiliary head advances accumulated by lookup. All mirrored heads and every tape cell remain in the original arbitrary frame. |
| `h1Seek_groups` | Unary-state lookup traverses one complete group per true and then the read-rank suffix. The result is the selected record boundary, with the state head on its false terminator. This is a single physical selector for all state counts and arbitrary source data frames. |
| `h1Seek_observe` | Capture the finite read rank and enter the unary state word in two silent moves of the auxiliary head. All mirrored heads stay fixed. |
| `h1ReadActions` | One state's ordered action list, before serialization. |
| `h1ReadActions_length` | Every state group has the same finite number of read vectors. |
| `h1ReadActions_at` | The finite rank used by the physical router selects the serializer's actual input/work-read record, including the tape-zero-first work ordering. |
| `h1Table_groups` | The public table writer is the serialization of these state groups. |
| `h1Table_cut` | Exact decomposition of the public table around a source transition. The selector skips `q` complete state groups followed by the captured read rank. This identifies the next record without any assumption about constant successor widths. |
| `h1Records_length` | A literal record list has at least as many bits as records. This is a consequence of the public action-length bound, with no table re-encoding. |
| `h1Run_headBound` | A unit work-head bound summed over a run. This is the only general head-bound argument needed for the auxiliary round envelope; mirrored and input heads have the stronger exact phase equations. **Promotion candidate:** a run form of `workTapePos_step_le`. |
| `h1Run_input` | Any machine whose actions keep the native input fixed preserves its position at every horizon. Public iteration transport supplies the run law. |
| `h1Groups_length` | Exact number of records in a prefix of complete state groups and one partial read group. This is only a list-length ledger. |
| `h1Seek_lookup` | Whole physical lookup, including finite observation and the unary-state loop. Its exit is first reached at the selected record boundary. The native input, all tape cells, physical output, and mirrored heads are unchanged. |
| `h1Unary_read` | Read a unary state word at any valid cell, including its terminating false. This uses the canonical buffer convention directly. |
| `h1SummaryState` | The summary auxiliary stores its stationary summary at zero, a blank at one, and the current unary state word starting at two. |
| `h1SummaryState_cell` | The state word and its left delimiter are a framed ordinary buffer, separated from the summary cell. |
| `h1SummaryState_update` | Updating the summary does not disturb the state word. |
| `h1Buffer_outside` | The canonical buffer is blank off its finite support. |
| `h1SummaryState_copy` | Copying a complete new state word into the cleared state region yields exactly the next summary/state layout. |
| `h1SummaryState_clear` | The catalog's framed clear erases only the state word, preserving the stationary summary and its blank separator. |
| `h1Seek_select` | Lookup selects the actual source transition in the public table. The physical input/work reads determine the finite rank. The returned table prefix contains at least `q` bits, a useful state-head and clearing ledger. |
| `h1TwoMoveTM` | Fixed two-cell routing between the summary cell and its state word. No parser or variable scan is involved. |
| `h1TwoMove_run` | Every prefix of the fixed two-cell routing move. The public one-action movement law is sufficient; all cells, input and output are framed. |
| `h1SeekPh_finite` | The selector's phase carriers are finite and have decidable equality. |
| `h1SeekPh_decidable` | Equality of selector phase states uses their finite carrier instances. |
| `h1RoundKey` | The finite schedule of one generic simulated transition. The live bit is retained only while restoring the heads after the successor was read. |
| `h1RoundPh` | The round's phase carriers, all independent of the coded state count. |
| `h1RoundPart` | All variable scans use their landed catalog machines. A table rewind first walks to the right delimiter, then uses `skipBackTM` on the whole word; this avoids requiring blank separators between encoded records. |
| `h1RoundExit` | A completed live successor returns to the round anchor; a simulated halt returns through a separate live exit. |
| `h1RoundRed` | The round's stationary, silent phase dispatches. A simulated halt goes to a live physical exit only after the action and all restoration have run. |
| `h1RoundTM` | One generic step block: lookup, clear the old state, execute the fixed payload, install its successor, and restore both auxiliary heads home. **Promotion candidate (host H2, step block; machine-library-design.md §14).** |
| `h1RoundPh_finite` | Finiteness of the round's physical control depends only on `k`. |
| `h1RoundPh_decidable` | The round's entry and live halt exit have decidable equality. |
| `h1RoundFinTM` | The generic step block as a finite binary machine. |
| `h1Data` | Canonical data frame for a round phase. The mirrored bank may contain arbitrary source tapes and positions, while the two auxiliary words and heads are explicit. The physical output prefix is independent of simulated output. |
| `h1Mirror_ne_summary` | A mirrored tape is distinct from the summary/state auxiliary. |
| `h1Data_shift` | Lookup's two head advances preserve the canonical data frame. |
| `h1RoundWindow` | During a round every simulated head is at its start or its single source-action endpoint. State renaming does not affect this predicate. |
| `h1Data_window` | A canonical phase frame has the round's start heads or its end heads, independently of both auxiliary positions and words. |
| `h1RoundSpan` | A segment of the already defined round host. Its strict prefix is live, excludes both round anchors, and satisfies the simulated-head envelope. |
| `h1RoundSpan_add` | Concatenate two proved segments by the public run-addition identity. This lemma only joins their strict-prefix predicates; it defines no host, loop, or alternative machine trace. |
| `h1Round_phase` | Lift one callee contract through the landed phase-host theorem. The endpoint is one silent dispatch after the callee's first selected exit. Liveness of every earlier callee state follows from halt absorption and its proved live endpoint. No machine trace is re-established here. |
| `h1At` | Enter a round phase with the data frame unchanged. |
| `h1Window_frame` | Transfer the simulated-head predicate across any data frame equality. Control types and auxiliary head positions may differ. |
| `h1Data_stateCell` | State-word cells of a canonical phase frame, with the left blank included. |
| `h1Round_prepare` | Clearing preparation restores the old unary-state head, erases its word, and returns to the summary cell before invoking the selected-record reader. All mirrored heads remain at their round-start positions throughout. |
| `h1Buffer_reads` | Literal cells of the middle word of a canonical concatenated buffer. Both cuts use the same framed append-read lemma. |
| `h1Round_payload` | Execute the inherited fixed payload, return to the cleared state word, then install the complete successor. The exit still precedes head restoration. The halting case consumes its false tag and keeps a live physical exit. |
| `h1Buffer_suffix` | A canonical buffer's suffix, including its right blank and all cells beyond it. This is the optional-list lookup law at a nonnegative offset. |
| `h1Round_restore` | Restore the table and successor-state heads after payload execution. The table scan reaches its right blank and the catalog reverse scan returns it to zero. The copied state word is then rewound to two, and the final fixed move returns the summary head to zero. The live/halt distinction is retained. |
| `h1Round_lookup` | Lift the proved physical selector into the full round. The result names its exact table cut, retaining both the state-size ledger and first-exit cut. |
| `h1Round_canonical` | Exact complete-round execution from a canonical data frame. The cost is bounded by fifty times the table length plus one, uniformly in the state count, input, and simulated time. Both continuation and halt use live exits. |
| `h1RoundRep` | Relation at the generic step block's seam. The first `k` work tapes mirror the source, and the native input position is its simulated input head. Auxiliary tape `k` holds the immutable public table; tape `k + 1` holds the output summary at zero, a blank at one, and the unary state at two. Both auxiliary heads are home at zero. Simulated halt has an empty state word. Physical control and the physical output prefix are deliberately independent. |
| `h1RoundRep_entry` | A related entry configuration is exactly the canonical round frame, with its arbitrary physical output prefix retained. This only unpacks the seam relation; it makes no assumption about the mirrored source tapes. |
| `h1Round_effect` | **Promotion candidate (host H2, step block; machine-library-design.md §14).** One finite physical machine `h1RoundFinTM k`, whose control depends only on `k`, realizes one transition of any canonized `k`-tape table. `h1RoundRep` fully specifies the seam. The table and unary state are data, never control. The source action is applied even when its successor is `none`; the block then reaches the separate live halt exit, after restoring both auxiliaries. |

## Continuation frontier (remaining inherited items 4–6)

1. **Startup and canonizer installation.** Load `⟨⟨bits t, α⟩, x⟩` using the sanctioned pair projections, `FinTM.exists_inputCallTM`, `exists_inputSeekTM`, and the inherited `exists_canonHeaderCall`. Instantiate the frozen witness of `exists_polyCanonizer` through `FinTM.exists_installCallTM`. Establish the new `h1RoundRep` seam: copied canonical `tableBitsK`, initial unary state at auxiliary cell 2, empty summary at cell 0, zero auxiliary heads, initial mirrored bank, and the correct simulated input position. Do not add a private canonizer, grammar parser, or header validator.
2. **Z1 and the binary clock.** Compose the one proved round using `vhostEmitTM_runFrom` and `counterLoopTM` over `bits t`. Prove both `counterLoopTM_run_done` (timeout) and `counterLoopTM_run_escape` (simulated halt), preserving the last-permitted-round case and the input device's boundary tag. The step block now supplies positive first return, live escape, silence, and a uniform per-round bound. Do not introduce a new host or assume an unproved fixed boundary tag at a loop seam.
3. **Verdict and joint ledger.** Use the inherited `summaryClock_accepts`, rather than another semantic acceptance proof. Combine polynomial startup with `t` rounds bounded by `50 * (|table| + 1)`, using `counterLoop_time_le`, the canonical code-length bound, and the verdict cost to obtain the frozen joint polynomial in `|α| + |x| + t + 1`.
4. **Note 50, then the headline.** Execute the physical **hosted and clocked H1** on a machine accepting exactly at deadline `t` and rejecting at `t - 1`, including `k ≥ 2` and first-step halt at deadline 1. Only then replace `exists_uniformSimulator`'s body. These note-50 tests have **not** been executed in this partial because that physical H1 has not been constructed. The step-block runtime tests below are not substitutes for them.

There are **no new helper sorries** and therefore no proved-modulo-new-helper chain to list. The original target's existing literal Proof sketch remains intact.

## Target disposition and admission census

| Target | Disposition |
|---|---|
| `Turing.MachineFormat.exists_uniformSimulator` | Open: original direct admission; this batch is 0/1. |
| `Turing.MachineFormat.exists_polyCanonizer` | Open and untouched; parallel batch owns it. |
| `Turing.exists_uniformMachineCode2` | Inherited proof unchanged, modulo the two B5a targets. |
| `Turing.exists_uniformMachineCode` | Same. |
| `Complexity.EXP_subset_POracle_EXPCOM` | Same. |
| `Complexity.POracle_EXPCOM_eq_EXP` | Inherited proof unchanged; no new admission path. |
| `Complexity.NPOracle_EXPCOM_eq_EXP` | Same. |
| `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM` | Same. |

The exact baseline set, recorded before editing, is unchanged at **16 declarations**. The permitted partial retains H1 in that set. The B5b summit and W2-S are already filled at this base; they have not been confused with the prior report's older direct-admission census. The S1210 detecting control is its **probe-local** `Complexity.exists_EXPCOM_decider`.

```text
# base sorry-warning set at the issue tree (integrate/fills-6 at b784ba0d: the eight fills-6 deliveries and the gate closes) over briefs/orders/b5a-fill-cont3.txt: one entry per declaration whose comment-stripped text contains `sorry` (Lean warns once per such declaration)
TuringMachine/Build/RecordTable: 6: exists_tableFindTM, exists_tableAppendTM, exists_recordTemplateTM, exists_recordInitTM, exists_recordValidTM, exists_recordNextTM
TuringMachine/CodeSimulator: 2: exists_polyCanonizer, exists_uniformSimulator
Diagonalization/NTimeHierarchy: 6: exists_timed_universal_NDTM, exists_ndAcceptsWithin_decider, exists_codeNDTM_accepts_linear, ntime_hierarchy, ntime_hierarchy_of_pos, NTIME_linear_ssubset_square
TuringMachine/Build/Zone: 2: exists_zoneShiftInTM, exists_zoneShiftOutTM
TOTAL 16
```

## Environment and verification

Lean is 4.25.0 (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), and mathlib remains pinned to `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. `lake exe cache get` was attempted; its internal ProofWidgets release operation failed. `lake exe cache unpack` unpacked 1,239 already-available cached files, sufficient for this closure. No `lake build` was invoked by this batch. All Lean checks, including probes and development checks, used the unmodified `scripts/lean_check_tree.sh`.

This runtime exposes `/proc/self/exe` but not its numeric own-PID equivalent used for Lean installation discovery. The supplied `self-exe-compat.c` redirects only that own-process `readlink` query; it does not modify Lean, proof checking, or reductions. `environment.sh` records the exact scope. Ordinary Lean installations do not need it. The exact 80-module closure was bootstrapped once and then rebuilt in the final sweep. Development logs, including failed proof attempts, are retained as development evidence and are not final gate logs.

Final results:

- Exact **80-module** final order: zero errors, fresh oleans, exactly the 16 baseline admission warnings by declaration name.
- `CodeSimulator`: zero errors, exactly two sorry warnings (canonizer and retained H1); all 98 new private declarations have empty recursive admission walks and only subsets of `[propext, Classical.choice, Quot.sound]`.
- Exact committed `B5aStatementsProbe`, `B5aContPreShip`, and `S1210StatementsProbe`: zero errors. B5a and S1210 retain their documented one probe-local admission each; the import probe has none. `ClassNP/TMSAT`, the additional B5a probe dependency beyond the 80-module order, was checked separately through the same script.
- Additive `S1210DetectingControl`: zero errors, explicitly detects `Complexity.exists_EXPCOM_decider` as a direct `sorryAx` user, while the committed census also detects it in both relevant derived consumers.
- Axiom prints and recursive admission walks cover H1, canonizer, all six targets 3–8, the B5b summit, Baker–Gill–Solovay, and every new helper. The retained headlines and inherited modulo paths are printed, not described as admission-free.
- The physical probe's production prefix is byte-identical to the delivered source. It exercises the actual new definitions in that source, with no replica machine, `native_decide`, `#eval!`, or new logical axiom. The independent axiom probe imports the real production olean and resolves its actual private declaration names.
- The required full before/after duplication screen uses the exact unmodified committed script and exact 34-file population. The incremental diagnostic was used only to find and factor issues during development.
- Both required style-lint runs have zero FAIL. Existing style warnings and unused-tactic/simp warnings are not hidden or disabled.

```text
PASS exact final order: 80/80 modules; no errors; fresh olean required by every check
PASS final sorry-warning set: exactly the 16 baseline declarations, unchanged (partial H1)
TCSlib/Complexity/TuringMachine/Build/RecordTable::exists_tableFindTM
TCSlib/Complexity/TuringMachine/Build/RecordTable::exists_tableAppendTM
TCSlib/Complexity/TuringMachine/Build/RecordTable::exists_recordTemplateTM
TCSlib/Complexity/TuringMachine/Build/RecordTable::exists_recordInitTM
TCSlib/Complexity/TuringMachine/Build/RecordTable::exists_recordValidTM
TCSlib/Complexity/TuringMachine/Build/RecordTable::exists_recordNextTM
TCSlib/Complexity/TuringMachine/CodeSimulator::exists_polyCanonizer
TCSlib/Complexity/TuringMachine/CodeSimulator::exists_uniformSimulator
TCSlib/Complexity/Diagonalization/NTimeHierarchy::exists_timed_universal_NDTM
TCSlib/Complexity/Diagonalization/NTimeHierarchy::exists_ndAcceptsWithin_decider
TCSlib/Complexity/Diagonalization/NTimeHierarchy::exists_codeNDTM_accepts_linear
TCSlib/Complexity/Diagonalization/NTimeHierarchy::ntime_hierarchy
TCSlib/Complexity/Diagonalization/NTimeHierarchy::ntime_hierarchy_of_pos
TCSlib/Complexity/Diagonalization/NTimeHierarchy::NTIME_linear_ssubset_square
TCSlib/Complexity/TuringMachine/Build/Zone::exists_zoneShiftInTM
TCSlib/Complexity/TuringMachine/Build/Zone::exists_zoneShiftOutTM
PASS CodeSimulator has exactly two sorry warnings: exists_polyCanonizer and exists_uniformSimulator
PASS B5aStatementsProbe: no errors; 1 expected probe-local sorry warnings
PASS B5aContPreShip: no errors; 0 expected probe-local sorry warnings
PASS S1210StatementsProbe: no errors; 1 expected probe-local sorry warnings
PASS S1210DetectingControl: no errors; 1 expected probe-local sorry warnings
PASS probe-extra-tmsat: no errors; 0 expected probe-local sorry warnings
PASS S1210 census detects its probe-local admission directly and through both derived consumers

PASS exact branch and required ancestor
PASS only owned file differs from base
PASS remove the new private gap and additive Fill appendix: byte-identical base source
PASS every inherited signature, body, docstring, import and module header unchanged
PASS no new admission, axiom, native_decide, or unsafe command
PASS git diff --check
Source lines: 4207; new private declarations: 98
Source SHA256: 986c470065359907b51f70cf3fdf008f1122cab1c588ef2883c0730fc027461d
PASS physical probe has an exactly source-identical production prefix
PASS exact committed probe: audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt
PASS exact committed probe: audits/evidence/b5a/B5aContPreShip.lean.txt
PASS exact committed probe: audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt

WARN  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  4207 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  4207 lines; 13 public / 176 private declarations
style_lint: 0 FAIL, 18 WARN over 58 files
style_lint: 0 FAIL, 0 WARN over 4 files
```

Physical step-block runtime cases (not note 50):

```text
PASS two-tape two-round run: 2463, 2660 physical steps; 1197 table bits
PASS two-tape first-transition halt, maximal read rank: 2684 steps
PASS right input boundary and variable successor: 2536 steps
PASS zero-tape empty-input halting action: 72 steps; 15 table bits
```

The two-tape table has three states and variable successor widths. Checks cover actual input/work read ranking, left-boundary crossings and right-boundary clamping, continuation and halt, halting writes/moves/emission, retained physical output, all intermediate simulated-head windows, auxiliary head bounds, home restoration, and final tape cells over the relevant finite support. The two-round case has one live return followed by a halt with simulated output `[true]`; the first-transition case starts at source state 2 and the maximal read rank. The zero-tape case exercises empty input at its right blank.

Final sweep tail:

```text
PASS TCSlib/Complexity/Diagonalization/NotTimeConstructible
CHECK TCSlib/Complexity/TuringMachine/NDCodes
PASS TCSlib/Complexity/TuringMachine/NDCodes
CHECK TCSlib/Complexity/Diagonalization/NTimeHierarchy
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:121:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:146:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:191:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:287:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:301:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:326:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/Diagonalization/NTimeHierarchy
CHECK TCSlib/Complexity/Diagonalization
PASS TCSlib/Complexity/Diagonalization
CHECK TCSlib/Complexity/TuringMachine/Build/Zone
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1112:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1148:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/TuringMachine/Build/Zone
CHECK TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
PASS TCSlib/Complexity/TuringMachine/Robustness/Bidirectional
CHECK TCSlib/Complexity/TuringMachine/Codes2Tape
PASS TCSlib/Complexity/TuringMachine/Codes2Tape
CHECK TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine
FINAL SWEEP PASS: 80 modules
```

## Duplication governance

**new copies: none.** There are nine new in-file screening pairs, all below 90%; no new cross-file pair, no removed baseline pair. The parallel canonizer continuation is invisible to this base and screen; its integration overlap must be measured separately as the brief requires. The inherited semantic clock is unchanged and the continuation frontier requires its single contract; the inherited payload proofs are unchanged and reused, and no chapter-1 interpreter step/parse proof was copied.

The development diagnostic initially flagged the common serializer enumeration and repeated public run-step/extension tactic scaffolding against short declarations elsewhere. The selector now uses one explicit three-group action list for its indexed-access proof and its bridge to the public table writer; first-step transfer is bound once per selector composition, and the general head bound uses the public telescoping-sum law. The final authoritative screen below, rather than an altered threshold or narrower population, is the delivered evidence.

| New in-file pair | Justification |
|---|---|
| `h1Round_payload` → `h1Data_shift` | The inherited payload's endpoint is re-expressed in the two-auxiliary canonical frame using the same `Cfg.ext`/`Fin.addCases` scaffolding; the payload contract itself is cited. |
| `h1Round_restore` → `h1Data_shift` | Finite-bank endpoint equations for catalog head restoration share the frame-extensionality pattern; restoration has different positions and no duplicate lookup trace. |
| `h1Round_prepare` → `h1Data_shift` | The old-state clearing path uses the same finite-bank frame equations, with catalog contracts supplying all variable scans. |
| `h1Round_restore` → `h1Round_prepare` | Distinct before/after payload paths instantiate the same public skip/reverse-skip contracts and `h1Round_phase`; the shared host proof is factored once. Different words, head endpoints, and live-exit routing require separate composition endpoints. |
| `h1Round_effect` → `h1Data_stateCell` | Both project the summary auxiliary with the same simplification constants; one exposes the state buffer and the other derives the summary update from the whole-round endpoint. |
| `h1ReadActions_at` → `h1Table_groups` | Both normalize the public serializer's list constructors/maps; one proves indexed selection and the other the grouped writer identity. |
| `h1Seek_groups` → `h1Seek_lookup` | One is the unary-state group loop, the other adds observation and its global ledger; common cuts and frame projection are joined with public run addition. |
| `h1Succ_trace` → `h1Succ_run` | The endpoint corollary cites the full prefix trace and only simplifies its final index; no second induction is present. |
| `h1Skip_path` → `h1Skip_run` | The all-prefix and endpoint contracts use the same public-host decomposition and inherited reader/tail contracts; neither re-proves those components. |

Exact added-pair output:

```text
   CodeSimulator.lean::h1ReadActions_at  reproduces  CodeSimulator.lean::h1Table_groups: 79/143 = 55%
   CodeSimulator.lean::h1Round_effect  reproduces  CodeSimulator.lean::h1Data_stateCell: 71/128 = 55%
   CodeSimulator.lean::h1Round_payload  reproduces  CodeSimulator.lean::h1Data_shift: 142/200 = 71%
   CodeSimulator.lean::h1Round_prepare  reproduces  CodeSimulator.lean::h1Data_shift: 115/200 = 57%
   CodeSimulator.lean::h1Round_restore  reproduces  CodeSimulator.lean::h1Data_shift: 115/200 = 57%
   CodeSimulator.lean::h1Round_restore  reproduces  CodeSimulator.lean::h1Round_prepare: 3055/5336 = 57%
   CodeSimulator.lean::h1Seek_groups  reproduces  CodeSimulator.lean::h1Seek_lookup: 1057/2000 = 53%
   CodeSimulator.lean::h1Skip_path  reproduces  CodeSimulator.lean::h1Skip_run: 547/1087 = 50%
   CodeSimulator.lean::h1Succ_trace  reproduces  CodeSimulator.lean::h1Succ_run: 124/240 = 52%
```

### Full before output

```text
declarations screened: 1920; copy pairs (target reproduces >= half of source): 2209; reproduced text: 735,760 chars
   Catalog.lean::f2_loopBody_step  reproduces  Loop.lean::loopBody_step: 1094/1094 = 100%
   Primitives.lean::splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_cut: 985/985 = 100%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Primitives.lean::splitEmbed_cut: 985/985 = 100%
   Catalog.lean::f2_pairCountTM  reproduces  Primitives.lean::pairCountTM: 860/860 = 100%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Primitives.lean::scanCopy_suffix: 850/850 = 100%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_pairExtractTM: 793/793 = 100%
   Catalog.lean::f2_pairExtractTM  reproduces  Primitives.lean::pairExtractTM: 793/793 = 100%
   Catalog.lean::f2_catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_copy: 731/731 = 100%
   Loop.lean::loop_find_run  reproduces  Catalog.lean::f2_loop_find_run: 678/678 = 100%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_find_run: 678/678 = 100%
   Loop.lean::loop_halted_run  reproduces  Catalog.lean::a2_loop_halted_run: 659/659 = 100%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_halted_run: 659/659 = 100%
   Catalog.lean::f2_splitPrepare_run  reproduces  Primitives.lean::splitPrepare_run: 632/632 = 100%
   Catalog.lean::f2_scanTrues_run  reproduces  Primitives.lean::scanTrues_run: 608/608 = 100%
   Primitives.lean::splitRestoreTM  reproduces  Catalog.lean::f2_splitRestoreTM: 562/562 = 100%
   Catalog.lean::f2_splitRestoreTM  reproduces  Primitives.lean::splitRestoreTM: 562/562 = 100%
   Catalog.lean::f2_splitBodyStateDecidableEq  reproduces  Primitives.lean::splitBodyStateDecidableEq: 537/537 = 100%
   Loop.lean::loop_rewind_bounded  reproduces  Catalog.lean::f2_loop_rewind_bounded: 514/514 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Loop.lean::loop_rewind_bounded: 514/514 = 100%
   Catalog.lean::f2_catalogPolyCost_le  reproduces  Primitives.lean::catalogPolyCost_le: 485/485 = 100%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::scanCopy_run: 482/482 = 100%
   Primitives.lean::incFixedTM  reproduces  Catalog.lean::f2_incFixedTM: 474/474 = 100%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::incFixedTM: 474/474 = 100%
   Primitives.lean::splitBody_envelope  reproduces  Catalog.lean::f2_splitBody_envelope: 466/466 = 100%
   Catalog.lean::f2_splitBody_envelope  reproduces  Primitives.lean::splitBody_envelope: 466/466 = 100%
   Primitives.lean::rawStripTM  reproduces  Catalog.lean::f2_rawStripTM: 461/461 = 100%
   Catalog.lean::f2_rawStripTM  reproduces  Primitives.lean::rawStripTM: 461/461 = 100%
   Catalog.lean::f2_loopBody_run  reproduces  Loop.lean::loopBody_run: 452/452 = 100%
   Catalog.lean::f2_splitEmit_run  reproduces  Primitives.lean::splitEmit_run: 440/440 = 100%
   Primitives.lean::catalogRewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Primitives.lean::catalogRewind: 435/435 = 100%
   Loop.lean::loopBodyTM  reproduces  Catalog.lean::f2_loopBodyTM: 428/428 = 100%
   Catalog.lean::f2_loopBodyTM  reproduces  Loop.lean::loopBodyTM: 428/428 = 100%
   EXPCOM.lean::UniformMachineCode  reproduces  Codes2Tape.lean::UniformMachineCode2: 419/419 = 100%
   Codes2Tape.lean::UniformMachineCode2  reproduces  EXPCOM.lean::UniformMachineCode: 419/419 = 100%
   Catalog.lean::f2_loopFuel_init  reproduces  Loop.lean::loopFuel_init: 410/410 = 100%
   Nondeterminism.lean::a2Buffer_write  reproduces  Loop.lean::loopBuffer_write: 408/408 = 100%
   Nondeterminism.lean::a2Buffer_write  reproduces  Catalog.lean::f2_loopBuffer_write: 408/408 = 100%
   Loop.lean::loopBuffer_write  reproduces  Nondeterminism.lean::a2Buffer_write: 408/408 = 100%
   Loop.lean::loopBuffer_write  reproduces  Catalog.lean::f2_loopBuffer_write: 408/408 = 100%
   Catalog.lean::f2_loopBuffer_write  reproduces  Nondeterminism.lean::a2Buffer_write: 408/408 = 100%
   Catalog.lean::f2_loopBuffer_write  reproduces  Loop.lean::loopBuffer_write: 408/408 = 100%
   Primitives.lean::emitter_first_entry  reproduces  Loop.lean::emCall_first_entry: 403/403 = 100%
   Loop.lean::emCall_first_entry  reproduces  Primitives.lean::emitter_first_entry: 403/403 = 100%
   Primitives.lean::splitPrepareTM  reproduces  Catalog.lean::f2_splitPrepareTM: 399/399 = 100%
   Catalog.lean::f2_splitPrepareTM  reproduces  Primitives.lean::splitPrepareTM: 399/399 = 100%
   Primitives.lean::catalogMarker_cases  reproduces  Catalog.lean::f2_catalogMarker_cases: 396/396 = 100%
   Catalog.lean::f2_catalogMarker_cases  reproduces  Primitives.lean::catalogMarker_cases: 396/396 = 100%
   Primitives.lean::pairDupTM  reproduces  Catalog.lean::f2_pairDupTM: 386/386 = 100%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::pairDupTM: 386/386 = 100%
   Catalog.lean::f2_pairCount_computes  reproduces  Primitives.lean::pairCount_computes: 383/383 = 100%
   Primitives.lean::catalogFirstEntry  reproduces  Catalog.lean::f2_catalogFirstEntry: 375/375 = 100%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Primitives.lean::catalogFirstEntry: 375/375 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::f2_splitPos_succ  reproduces  Primitives.lean::splitPos_succ: 353/353 = 100%
   Primitives.lean::incFixed_cases  reproduces  Catalog.lean::f2_incFixed_cases: 352/352 = 100%
   Catalog.lean::f2_incFixed_cases  reproduces  Primitives.lean::incFixed_cases: 352/352 = 100%
   Catalog.lean::f2_loopBody_stop  reproduces  Loop.lean::loopBody_stop: 346/346 = 100%
   Catalog.lean::f2_loopReplay_run  reproduces  Loop.lean::loopReplay_run: 345/345 = 100%
   Loop.lean::loop_first_halt  reproduces  Catalog.lean::f2_loop_first_halt: 341/341 = 100%
   Catalog.lean::f2_loop_first_halt  reproduces  Loop.lean::loop_first_halt: 341/341 = 100%
   Primitives.lean::splitEmitTM  reproduces  Catalog.lean::f2_splitEmitTM: 327/327 = 100%
   Catalog.lean::f2_splitEmitTM  reproduces  Primitives.lean::splitEmitTM: 327/327 = 100%
   Primitives.lean::emitter_take_succ_eq  reproduces  Nondeterminism.lean::e3c_take_succ_eq: 291/291 = 100%
   Nondeterminism.lean::e3c_take_succ_eq  reproduces  Primitives.lean::emitter_take_succ_eq: 291/291 = 100%
   Catalog.lean::f2_loopCopy_erase  reproduces  Loop.lean::loopCopy_erase: 285/285 = 100%
   Primitives.lean::splitLoop_bound  reproduces  Catalog.lean::f2_splitLoop_bound: 276/276 = 100%
   Catalog.lean::f2_splitLoop_bound  reproduces  Primitives.lean::splitLoop_bound: 276/276 = 100%
   Loop.lean::loopFrame  reproduces  Catalog.lean::f2_loopFrame: 270/270 = 100%
   Catalog.lean::f2_loopFrame  reproduces  Loop.lean::loopFrame: 270/270 = 100%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Admin_apply: 264/264 = 100%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 264/264 = 100%
   Loop.lean::loop_output_length_le  reproduces  Catalog.lean::f2_loop_output_length_le: 254/254 = 100%
   Catalog.lean::f2_loop_output_length_le  reproduces  Loop.lean::loop_output_length_le: 254/254 = 100%
   Primitives.lean::pairValidTM  reproduces  Catalog.lean::f2_pairValidTM: 249/249 = 100%
   Catalog.lean::f2_pairValidTM  reproduces  Primitives.lean::pairValidTM: 249/249 = 100%
   Catalog.lean::f2_loopFuel_run  reproduces  Loop.lean::loopFuel_run: 230/230 = 100%
   Primitives.lean::emitter_bits_injective  reproduces  Nondeterminism.lean::e3c_bits_injective: 227/227 = 100%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Primitives.lean::emitter_bits_injective: 227/227 = 100%
   UniversalInterpreter.lean::universalStateTape_append  reproduces  Universal.lean::timedCut_StateTape_append: 218/218 = 100%
   Universal.lean::timedCut_StateTape_append  reproduces  UniversalInterpreter.lean::universalStateTape_append: 218/218 = 100%
   Catalog.lean::f2_splitPos_read  reproduces  Primitives.lean::splitPos_read: 215/215 = 100%
   Loop.lean::loopBodyCfg  reproduces  Catalog.lean::f2_loopBodyCfg: 212/212 = 100%
   Catalog.lean::f2_loopBodyCfg  reproduces  Loop.lean::loopBodyCfg: 212/212 = 100%
   Primitives.lean::catalogPrefixTM  reproduces  Catalog.lean::f2_catalogPrefixTM: 209/209 = 100%
   Catalog.lean::f2_catalogPrefixTM  reproduces  Primitives.lean::catalogPrefixTM: 209/209 = 100%
   UniversalStartup.lean::universal_pair_separator  reproduces  Universal.lean::timed_pair_separator: 207/207 = 100%
   Universal.lean::timed_pair_separator  reproduces  UniversalStartup.lean::universal_pair_separator: 207/207 = 100%
   Catalog.lean::f2_splitStep_orbit  reproduces  Primitives.lean::splitStep_orbit: 201/201 = 100%
   Catalog.lean::f2_splitCountCfg  reproduces  Primitives.lean::splitCountCfg: 201/201 = 100%
   UniversalBlock.lean::universalActionBits_decode  reproduces  Universal.lean::timedCut_ActionBits_decode: 191/191 = 100%
   Universal.lean::timedCut_ActionBits_decode  reproduces  UniversalBlock.lean::universalActionBits_decode: 191/191 = 100%
   Primitives.lean::splitRewindTM  reproduces  Catalog.lean::f2_splitRewindTM: 185/185 = 100%
   Catalog.lean::f2_splitRewindTM  reproduces  Primitives.lean::splitRewindTM: 185/185 = 100%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Universal.lean::timedCaptureCfg: 184/184 = 100%
   Universal.lean::timedCaptureCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 184/184 = 100%
   Catalog.lean::f2_lenCfg  reproduces  Primitives.lean::lenCfg: 177/177 = 100%
   Primitives.lean::anyTrueTM  reproduces  Catalog.lean::f2_anyTrueTM: 175/175 = 100%
   Catalog.lean::f2_anyTrueTM  reproduces  Primitives.lean::anyTrueTM: 175/175 = 100%
   Catalog.lean::f2_scanCfg_read  reproduces  Primitives.lean::scanCfg_read: 172/172 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Primitives.lean::splitCountAction  reproduces  Catalog.lean::f2_splitCountAction: 166/166 = 100%
   Catalog.lean::f2_splitCountAction  reproduces  Primitives.lean::splitCountAction: 166/166 = 100%
   Catalog.lean::f2_catalogPolyTape_write  reproduces  Primitives.lean::catalogPolyTape_write: 165/165 = 100%
   UniversalBlock.lean::universal_header_bound  reproduces  Universal.lean::timed_header_bound: 153/153 = 100%
   Universal.lean::timed_header_bound  reproduces  UniversalBlock.lean::universal_header_bound: 153/153 = 100%
   Loop.lean::loopControlAction  reproduces  Catalog.lean::f2_loopControlAction: 150/150 = 100%
   Catalog.lean::f2_loopControlAction  reproduces  Loop.lean::loopControlAction: 150/150 = 100%
   Catalog.lean::f2_loopCall  reproduces  Loop.lean::loopCall: 141/141 = 100%
   UniversalBlock.lean::universalActions  reproduces  Universal.lean::timedCut_Actions: 140/140 = 100%
   Universal.lean::timedCut_Actions  reproduces  UniversalBlock.lean::universalActions: 140/140 = 100%
   Nondeterminism.lean::e3ChoiceVerifier  reproduces  Nondeterminism.lean::choiceVerifier: 136/136 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::f2_loopValue_bits  reproduces  Loop.lean::loopValue_bits: 135/135 = 100%
   Primitives.lean::SplitBodyState  reproduces  Catalog.lean::f2_SplitBodyState: 134/134 = 100%
   Catalog.lean::f2_SplitBodyState  reproduces  Primitives.lean::SplitBodyState: 134/134 = 100%
   Loop.lean::loopReplayTM  reproduces  Catalog.lean::f2_loopReplayTM: 130/130 = 100%
   Catalog.lean::f2_loopReplayTM  reproduces  Loop.lean::loopReplayTM: 130/130 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Nondeterminism.lean::e3_split_spec  reproduces  Nondeterminism.lean::certificateSplit_spec: 125/125 = 100%
   Nondeterminism.lean::certificateSplit_spec  reproduces  Nondeterminism.lean::e3_split_spec: 125/125 = 100%
   Loop.lean::loopFuelSource  reproduces  Catalog.lean::f2_loopFuelSource: 122/122 = 100%
   Catalog.lean::f2_splitPrepareReady  reproduces  Primitives.lean::splitPrepareReady: 122/122 = 100%
   Catalog.lean::f2_loopFuelSource  reproduces  Loop.lean::loopFuelSource: 122/122 = 100%
   UniversalStartup.lean::universal_live_before  reproduces  Universal.lean::timedCut_live_before: 121/121 = 100%
   Universal.lean::timedCut_live_before  reproduces  UniversalStartup.lean::universal_live_before: 121/121 = 100%
   Catalog.lean::f2_loopBodySource  reproduces  Loop.lean::loopBodySource: 119/119 = 100%
   Primitives.lean::catalogBuffer_erase  reproduces  Catalog.lean::f2_catalogBuffer_erase: 118/118 = 100%
   Loop.lean::emCall_erase_last  reproduces  Primitives.lean::catalogBuffer_erase: 118/118 = 100%
   Loop.lean::emCall_erase_last  reproduces  Catalog.lean::f2_catalogBuffer_erase: 118/118 = 100%
   Catalog.lean::f2_catalogBuffer_erase  reproduces  Primitives.lean::catalogBuffer_erase: 118/118 = 100%
   UniversalInterpreter.lean::universalInterpreterInitial  reproduces  Universal.lean::timedCut_InterpreterInitial: 113/113 = 100%
   Universal.lean::timedCut_InterpreterInitial  reproduces  UniversalInterpreter.lean::universalInterpreterInitial: 113/113 = 100%
   Primitives.lean::splitSafe_add  reproduces  Catalog.lean::f2_splitSafe_add: 110/110 = 100%
   Catalog.lean::f2_splitSafe_add  reproduces  Primitives.lean::splitSafe_add: 110/110 = 100%
   Catalog.lean::f2_loopCopy_final  reproduces  Loop.lean::loopCopy_final: 110/110 = 100%
   Primitives.lean::splitSafe_one  reproduces  Catalog.lean::f2_splitSafe_one: 107/107 = 100%
   Catalog.lean::f2_splitSafe_one  reproduces  Primitives.lean::splitSafe_one: 107/107 = 100%
   Catalog.lean::f2_splitRestoreScan  reproduces  Primitives.lean::splitRestoreScan: 106/106 = 100%
   Primitives.lean::catalogFind_congr  reproduces  Nondeterminism.lean::e3_find_congr: 104/104 = 100%
   Primitives.lean::catalogFind_congr  reproduces  Catalog.lean::f2_catalogFind_congr: 104/104 = 100%
   Nondeterminism.lean::e3_find_congr  reproduces  Primitives.lean::catalogFind_congr: 104/104 = 100%
   Nondeterminism.lean::e3_find_congr  reproduces  Catalog.lean::f2_catalogFind_congr: 104/104 = 100%
   Catalog.lean::f2_catalogFind_congr  reproduces  Primitives.lean::catalogFind_congr: 104/104 = 100%
   Catalog.lean::f2_catalogFind_congr  reproduces  Nondeterminism.lean::e3_find_congr: 104/104 = 100%
   UniversalInterpreter.lean::universalInterpreterBase  reproduces  Universal.lean::timedCut_InterpreterBase: 102/102 = 100%
   Universal.lean::timedCut_InterpreterBase  reproduces  UniversalInterpreter.lean::universalInterpreterBase: 102/102 = 100%
   Loop.lean::loopBodyTM  reproduces  Oracle.lean::Action.extend: 101/101 = 100%
   Catalog.lean::f2_loopBodyTM  reproduces  Oracle.lean::Action.extend: 101/101 = 100%
   Catalog.lean::f2_splitPrepareScan  reproduces  Primitives.lean::splitPrepareScan: 97/97 = 100%
   Catalog.lean::f2_splitSafe_join  reproduces  Primitives.lean::splitSafe_join: 95/95 = 100%
   Loop.lean::loop_orbit_inv  reproduces  Catalog.lean::f2_loop_orbit_inv: 94/94 = 100%
   Catalog.lean::f2_loop_orbit_inv  reproduces  Loop.lean::loop_orbit_inv: 94/94 = 100%
   Catalog.lean::f2_loopBorrowPos_le  reproduces  Loop.lean::loopBorrowPos_le: 93/93 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   Catalog.lean::computesFunInTime_pairEncodeFixed_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairEncodeFixed: 91/91 = 100%
   Loop.lean::loopFuelCfg  reproduces  Catalog.lean::f2_loopFuelCfg: 90/90 = 100%
   Catalog.lean::f2_loopFuelCfg  reproduces  Loop.lean::loopFuelCfg: 90/90 = 100%
   Primitives.lean::CatalogPolyControl  reproduces  Catalog.lean::f2_CatalogPolyControl: 89/89 = 100%
   Nondeterminism.lean::a2Buffer_read  reproduces  Loop.lean::loopBuffer_read: 89/89 = 100%
   Nondeterminism.lean::a2Buffer_read  reproduces  Catalog.lean::f2_loopBuffer_read: 89/89 = 100%
   Loop.lean::loopBuffer_read  reproduces  Nondeterminism.lean::a2Buffer_read: 89/89 = 100%
   Loop.lean::loopBuffer_read  reproduces  Catalog.lean::f2_loopBuffer_read: 89/89 = 100%
   Catalog.lean::f2_loopBuffer_read  reproduces  Nondeterminism.lean::a2Buffer_read: 89/89 = 100%
   Catalog.lean::f2_loopBuffer_read  reproduces  Loop.lean::loopBuffer_read: 89/89 = 100%
   Catalog.lean::f2_CatalogPolyControl  reproduces  Primitives.lean::CatalogPolyControl: 89/89 = 100%
   UniversalInterpreter.lean::universalEval_reads  reproduces  Universal.lean::timedCut_Eval_reads: 88/88 = 100%
   Universal.lean::timedCut_Eval_reads  reproduces  UniversalInterpreter.lean::universalEval_reads: 88/88 = 100%
   Loop.lean::loop_fuel_width  reproduces  Catalog.lean::f2_loop_fuel_width: 87/87 = 100%
   Catalog.lean::f2_loop_fuel_width  reproduces  Loop.lean::loop_fuel_width: 87/87 = 100%
   Catalog.lean::f2_loopFrame_payload  reproduces  Loop.lean::loopFrame_payload: 79/79 = 100%
   Nondeterminism.lean::contSplitWord  reproduces  CertShell.lean::certSplitWord: 74/74 = 100%
   CertShell.lean::certSplitWord  reproduces  Nondeterminism.lean::contSplitWord: 74/74 = 100%
   UniversalBlock.lean::universalHeader  reproduces  Universal.lean::timedCut_Header: 73/73 = 100%
   Universal.lean::timedCut_Header  reproduces  UniversalBlock.lean::universalHeader: 73/73 = 100%
   UniversalBlock.lean::universalActions_lookup  reproduces  Universal.lean::timedCut_Actions_lookup: 68/68 = 100%
   Universal.lean::timedCut_Actions_lookup  reproduces  UniversalBlock.lean::universalActions_lookup: 68/68 = 100%
   UniversalInterpreter.lean::universal_table_read  reproduces  Universal.lean::timedCut_table_read: 61/61 = 100%
   Universal.lean::timedCut_table_read  reproduces  UniversalInterpreter.lean::universal_table_read: 61/61 = 100%
   Primitives.lean::splitRestoreClean  reproduces  Catalog.lean::f2_splitRestoreClean: 61/61 = 100%
   Catalog.lean::f2_splitRestoreClean  reproduces  Primitives.lean::splitRestoreClean: 61/61 = 100%
   Catalog.lean::f2_loopFlag_clear  reproduces  Loop.lean::loopFlag_clear: 60/60 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Primitives.lean::emitterSplit_find  reproduces  Primitives.lean::splitFind_eq: 227/228 = 100%
   UniversalBlock.lean::universal_apply_record  reproduces  Universal.lean::timed_apply_record: 1357/1366 = 99%
   Universal.lean::timed_apply_record  reproduces  UniversalBlock.lean::universal_apply_record: 1357/1366 = 99%
   Loop.lean::loopBody_run  reproduces  Catalog.lean::f2_loopBody_run: 452/455 = 99%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   UniversalInterpreter.lean::universalStartupBound  reproduces  Universal.lean::timedStartupBound: 130/131 = 99%
   Universal.lean::timedStartupBound  reproduces  UniversalInterpreter.lean::universalStartupBound: 130/131 = 99%
   MathlibBridge.lean::codePrimBitsNat  reproduces  MathlibBridge.lean::bridgePrimNumber: 128/129 = 99%
   MathlibBridge.lean::bridgePrimNumber  reproduces  MathlibBridge.lean::codePrimBitsNat: 128/129 = 99%
   Catalog.lean::f2_loopHost_contracts  reproduces  Loop.lean::loopHost_contracts: 3565/3596 = 99%
   Primitives.lean::emitterToken_double  reproduces  Primitives.lean::emitterToken_separator: 215/217 = 99%
   Universal.lean::timedCut_read_fixed  reproduces  UniversalBlock.lean::universal_read_fixed: 1863/1881 = 99%
   UniversalBlock.lean::universal_skip_records  reproduces  Universal.lean::timedCut_skip_records: 729/737 = 99%
   Universal.lean::timedCut_skip_records  reproduces  UniversalBlock.lean::universal_skip_records: 729/738 = 99%
   Catalog.lean::f2_catalogPolyUnaryTM  reproduces  Primitives.lean::catalogPolyUnaryTM: 788/798 = 99%
   Catalog.lean::f2_extract_run  reproduces  Primitives.lean::extract_run: 1830/1854 = 99%
   Loop.lean::loopBody_step  reproduces  Catalog.lean::f2_loopBody_step: 1094/1109 = 99%
   Universal.lean::timedCut_skip_groups  reproduces  UniversalBlock.lean::universal_skip_groups: 1873/1900 = 99%
   Nondeterminism.lean::choiceVerifier  reproduces  Nondeterminism.lean::e3ChoiceVerifier: 136/138 = 99%
   Primitives.lean::scanTrues_run  reproduces  Catalog.lean::f2_scanTrues_run: 608/617 = 99%
   Primitives.lean::splitStep_orbit  reproduces  Catalog.lean::f2_splitStep_orbit: 201/204 = 99%
   Primitives.lean::splitCountCfg  reproduces  Catalog.lean::f2_splitCountCfg: 201/204 = 99%
   Catalog.lean::f2_extract_suffix  reproduces  Primitives.lean::extract_suffix: 1125/1142 = 99%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::splitEmit_double: 1402/1424 = 98%
   Primitives.lean::lenCfg  reproduces  Catalog.lean::f2_lenCfg: 177/180 = 98%
   Catalog.lean::f2_catalogPoly_loop  reproduces  Primitives.lean::catalogPoly_loop: 3777/3842 = 98%
   Loop.lean::loopBody_stop  reproduces  Catalog.lean::f2_loopBody_stop: 346/352 = 98%
   Loop.lean::loopReplay_run  reproduces  Catalog.lean::f2_loopReplay_run: 345/351 = 98%
   Catalog.lean::f2_splitBodyTM  reproduces  Primitives.lean::splitBodyTM: 676/688 = 98%
   Primitives.lean::catalogPolyCost_le  reproduces  Catalog.lean::f2_catalogPolyCost_le: 485/494 = 98%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  Primitives.lean::catalogPoly_rewind: 1010/1030 = 98%
   Primitives.lean::splitEmit_run  reproduces  Catalog.lean::f2_splitEmit_run: 440/449 = 98%
   Catalog.lean::f2_loopHost  reproduces  Loop.lean::loopHostM: 2368/2417 = 98%
   Loop.lean::loopCopy_erase  reproduces  Catalog.lean::f2_loopCopy_erase: 285/291 = 98%
   Primitives.lean::scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 850/868 = 98%
   Loop.lean::loopCall  reproduces  Catalog.lean::f2_loopCall: 141/144 = 98%
   Catalog.lean::f2_splitLoop_result  reproduces  Primitives.lean::splitLoop_result: 226/231 = 98%
   Loop.lean::loopBorrowPos_le  reproduces  Nondeterminism.lean::a2BorrowPos_le: 89/91 = 98%
   Catalog.lean::f2_loopBorrowPos_le  reproduces  Nondeterminism.lean::a2BorrowPos_le: 89/91 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalBlock.lean::universal_apply_record  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   Universal.lean::timedCut_Interpreter_first  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Primitives.lean::pairCount_computes  reproduces  Catalog.lean::f2_pairCount_computes: 383/392 = 98%
   Primitives.lean::emitterP2SmallIndex  reproduces  Primitives.lean::emitterP2PairIndex: 207/212 = 98%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::extract_replay: 567/581 = 98%
   Loop.lean::loopBodySource  reproduces  Catalog.lean::f2_loopBodySource: 119/122 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Catalog.lean::f2_rawStrip_erase  reproduces  Primitives.lean::rawStrip_erase: 345/354 = 97%
   Loop.lean::loopFuel_run  reproduces  Catalog.lean::f2_loopFuel_run: 230/236 = 97%
   Catalog.lean::f2_splitCount_run  reproduces  Primitives.lean::splitCount_run: 898/922 = 97%
   Nondeterminism.lean::choiceVerifier_no_split  reproduces  Nondeterminism.lean::e3_choice_no_split: 145/149 = 97%
   Universal.lean::timedCut_skip_fixed  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 647/665 = 97%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::rawStrip_replay: 395/406 = 97%
   Primitives.lean::splitPos_read  reproduces  Catalog.lean::f2_splitPos_read: 215/221 = 97%
   Universal.lean::timedCut_table_rewind  reproduces  UniversalInterpreter.lean::universal_table_rewind: 637/655 = 97%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Primitives.lean::catalogPoly_unary_computes: 1223/1258 = 97%
   Primitives.lean::catalogPrefixTM_copy  reproduces  Catalog.lean::f2_catalogPrefixTM_copy: 731/752 = 97%
   Loop.lean::loopFuel_init  reproduces  Catalog.lean::f2_loopFuel_init: 410/422 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Universal.lean::timedCut_select  reproduces  UniversalBlock.lean::universal_select: 2103/2166 = 97%
   UniversalBlock.lean::universal_skip_record  reproduces  Universal.lean::timedCut_skip_record: 797/821 = 97%
   Catalog.lean::f2_splitEmitCfg  reproduces  Primitives.lean::splitEmitCfg: 97/100 = 97%
   Universal.lean::timedCut_skip_unary  reproduces  UniversalBlock.lean::universal_skip_unary: 1160/1196 = 97%
   Primitives.lean::scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_run: 482/497 = 97%
   UniversalBlock.lean::universal_read_fixed  reproduces  Universal.lean::timedCut_read_fixed: 1863/1921 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Primitives.lean::splitSafe_join  reproduces  Catalog.lean::f2_splitSafe_join: 95/98 = 97%
   Catalog.lean::f2_splitFind_eq  reproduces  Primitives.lean::splitFind_eq: 221/228 = 97%
   Primitives.lean::catalogPolyUnaryTM  reproduces  Catalog.lean::f2_catalogPolyUnaryTM: 788/813 = 97%
   Catalog.lean::f2_scanCopy_finish  reproduces  Primitives.lean::scanCopy_finish: 249/257 = 97%
   Loop.lean::loopBorrowPos_le  reproduces  Catalog.lean::f2_loopBorrowPos_le: 93/96 = 97%
   Primitives.lean::scanTrues_run  reproduces  Primitives.lean::scanStep_right: 153/158 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Primitives.lean::emitterP2_right_frame  reproduces  Primitives.lean::emitterP2_left_frame: 273/282 = 97%
   Catalog.lean::f2_lenStart  reproduces  Primitives.lean::lenStart: 1606/1659 = 97%
   Catalog.lean::f2_extract_block  reproduces  Primitives.lean::extract_block: 633/654 = 97%
   Primitives.lean::splitBodyStateDecidableEq  reproduces  Catalog.lean::f2_splitBodyStateDecidableEq: 537/555 = 97%
   Universal.lean::timedCut_skip_record  reproduces  UniversalBlock.lean::universal_skip_record: 797/824 = 97%
   Primitives.lean::pairCountTM  reproduces  Catalog.lean::f2_pairCountTM: 860/890 = 97%
   Primitives.lean::scanCfg_read  reproduces  Catalog.lean::f2_scanCfg_read: 172/178 = 97%
   UniversalBlock.lean::universal_skip_groups  reproduces  Universal.lean::timedCut_skip_groups: 1873/1939 = 97%
   Primitives.lean::splitFind_eq  reproduces  Primitives.lean::emitterSplit_find: 227/235 = 97%
   Primitives.lean::extract_replay  reproduces  Catalog.lean::f2_extract_replay: 567/587 = 97%
   Catalog.lean::f2_loopHost_replay  reproduces  Loop.lean::loopHost_replay: 1032/1069 = 97%
   Primitives.lean::catalogPolyTape_write  reproduces  Catalog.lean::f2_catalogPolyTape_write: 165/171 = 96%
   Primitives.lean::emitterP2_left_frame  reproduces  Primitives.lean::emitterP2_right_frame: 273/283 = 96%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Primitives.lean::splitEmit_suffix: 1056/1095 = 96%
   Catalog.lean::f2_splitCount_over  reproduces  Primitives.lean::splitCount_over: 132/137 = 96%
   Loop.lean::loopFrame_payload  reproduces  Catalog.lean::f2_loopFrame_payload: 79/82 = 96%
   Universal.lean::timedCut_initial_skip  reproduces  UniversalInterpreter.lean::universal_initial_skip: 934/970 = 96%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::extract_rewind: 718/746 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Loop.lean::loopHost_frame_replay: 888/923 = 96%
   Catalog.lean::f2_splitRestore_scan  reproduces  Primitives.lean::splitRestore_scan: 799/831 = 96%
   Catalog.lean::f2_extract_first  reproduces  Primitives.lean::extract_first: 274/285 = 96%
   Catalog.lean::f2_extract_finish  reproduces  Primitives.lean::extract_finish: 595/619 = 96%
   Catalog.lean::f2_rawStrip_finish  reproduces  Primitives.lean::rawStrip_finish: 270/281 = 96%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::computesFunInTime_pairConcat: 147/153 = 96%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::rawStrip_replay: 390/406 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::rawStrip_replay: 390/406 = 96%
   Catalog.lean::f2_loopReplay_step  reproduces  Loop.lean::loopReplay_step: 316/329 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Universal.lean::timedCut_prepare_next  reproduces  UniversalBlock.lean::universal_prepare_next: 1959/2040 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   UniversalStartup.lean::universalCapture_transfer  reproduces  Universal.lean::timedCapture_transfer: 119/124 = 96%
   Primitives.lean::splitPos_succ  reproduces  Catalog.lean::f2_splitPos_succ: 353/368 = 96%
   Primitives.lean::extract_run  reproduces  Catalog.lean::f2_extract_run: 1830/1908 = 96%
   Primitives.lean::rawStrip_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 395/412 = 96%
   Catalog.lean::f2_catalogPrefixTM_computes  reproduces  Primitives.lean::catalogPrefixTM_computes: 369/385 = 96%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::pairDup_double: 1127/1176 = 96%
   Primitives.lean::splitBodyTM  reproduces  Catalog.lean::f2_splitBodyTM: 676/706 = 96%
   Loop.lean::loopValue_bits  reproduces  Catalog.lean::f2_loopValue_bits: 135/141 = 96%
   Nondeterminism.lean::a2BorrowPos_le  reproduces  Loop.lean::loopBorrowPos_le: 89/93 = 96%
   Nondeterminism.lean::certificateSplit_none_iff  reproduces  Nondeterminism.lean::e3_split_none_iff: 155/162 = 96%
   Primitives.lean::emitterP2_body_erase_right  reproduces  Primitives.lean::emitterP2_body_erase_left: 1078/1127 = 96%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedCut_unary_copy: 942/985 = 96%
   UniversalBlock.lean::universal_select  reproduces  Universal.lean::timedCut_select: 2103/2199 = 96%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_double: 1402/1466 = 96%
   Catalog.lean::f2_lenParse_block  reproduces  Primitives.lean::lenParse_block: 700/732 = 96%
   UniversalInterpreter.lean::universal_state_rewind  reproduces  Universal.lean::timedCut_state_rewind: 393/411 = 96%
   Universal.lean::timedCut_state_rewind  reproduces  UniversalInterpreter.lean::universal_state_rewind: 393/411 = 96%
   Catalog.lean::f2_loopControl_payload  reproduces  Loop.lean::loopControl_payload: 235/246 = 96%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 827/866 = 95%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 827/866 = 95%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::splitRestore_rewind: 754/790 = 95%
   Universal.lean::timedCut_unary_copy  reproduces  UniversalInterpreter.lean::universal_unary_copy: 942/987 = 95%
   Catalog.lean::f2_splitEmit_separator  reproduces  Primitives.lean::splitEmit_separator: 730/765 = 95%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Primitives.lean::splitLoop_result  reproduces  Catalog.lean::f2_splitLoop_result: 226/237 = 95%
   Primitives.lean::computesFunInTime_stripLast  reproduces  Catalog.lean::f2_strip_linear: 1616/1695 = 95%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   Primitives.lean::splitPrepareReady  reproduces  Catalog.lean::f2_splitPrepareReady: 122/128 = 95%
   Catalog.lean::f2_extract_replay_finish  reproduces  Primitives.lean::extract_replay_finish: 284/298 = 95%
   Loop.lean::loopFlag_clear  reproduces  Catalog.lean::f2_loopFlag_clear: 60/63 = 95%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 719/755 = 95%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::f2_splitCount_run: 898/943 = 95%
   UniversalBlock.lean::universal_serialization_actions  reproduces  UniversalInterpreter.lean::universal_serialization_header: 589/619 = 95%
   Universal.lean::timedCut_serialization_actions  reproduces  UniversalInterpreter.lean::universal_serialization_header: 589/619 = 95%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_halted_run: 627/659 = 95%
   Loop.lean::loop_run  reproduces  Catalog.lean::a2_loop_halted_run: 627/659 = 95%
   Primitives.lean::emitterP2_body_erase_left  reproduces  Primitives.lean::emitterP2_body_erase_right: 1078/1134 = 95%
   Nondeterminism.lean::e3_choice_append  reproduces  Nondeterminism.lean::choiceVerifier_append: 192/202 = 95%
   Primitives.lean::rawStrip_erase  reproduces  Catalog.lean::f2_rawStrip_erase: 345/363 = 95%
   Catalog.lean::f2_loopHost_accept  reproduces  Loop.lean::loopHost_accept: 2127/2238 = 95%
   Catalog.lean::f2_loopDebit_value  reproduces  Loop.lean::loopDebit_value: 187/197 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Loop.lean::loopHostM  reproduces  Catalog.lean::f2_loopHost: 2368/2495 = 95%
   Catalog.lean::f2_rawStrip_trim  reproduces  Primitives.lean::rawStrip_trim: 575/606 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::computesFunInTime_pairFst: 147/155 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Loop.lean::loopCopy_final  reproduces  Catalog.lean::f2_loopCopy_final: 110/116 = 95%
   UniversalBlock.lean::universal_serialization_actions  reproduces  Universal.lean::timedCut_serialization_actions: 767/809 = 95%
   Universal.lean::timedCut_serialization_actions  reproduces  UniversalBlock.lean::universal_serialization_actions: 767/809 = 95%
   Nondeterminism.lean::a2_compile  reproduces  Nondeterminism.lean::b2_compile: 924/975 = 95%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_scan: 605/639 = 95%
   Primitives.lean::extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 390/412 = 95%
   Primitives.lean::splitRestoreScan  reproduces  Catalog.lean::f2_splitRestoreScan: 106/112 = 95%
   Primitives.lean::splitPrepare_run  reproduces  Catalog.lean::f2_splitPrepare_run: 632/668 = 95%
   Catalog.lean::f2_catalogPoly_copy  reproduces  Primitives.lean::catalogPoly_copy: 665/703 = 95%
   Catalog.lean::f2_catalogPoly_start  reproduces  Primitives.lean::catalogPoly_start: 833/881 = 95%
   Primitives.lean::catalogPoly_loop  reproduces  Catalog.lean::f2_catalogPoly_loop: 3777/3995 = 95%
   Primitives.lean::extract_suffix  reproduces  Catalog.lean::f2_extract_suffix: 1125/1190 = 95%
   Primitives.lean::catalogPoly_unary_computes  reproduces  Catalog.lean::f2_catalogPoly_unary_computes: 1223/1294 = 95%
   Primitives.lean::catalogPoly_rewind  reproduces  Catalog.lean::f2_catalogPoly_rewind: 1010/1069 = 94%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_bank_initial: 3070/3250 = 94%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Interpreter_first: 272/288 = 94%
   Primitives.lean::lenStart  reproduces  Catalog.lean::f2_lenStart: 1606/1701 = 94%
   Loop.lean::loopControl_payload  reproduces  Catalog.lean::f2_loopControl_payload: 235/249 = 94%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Eval_reads: 83/88 = 94%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   Universal.lean::timedCut_Admin_apply  reproduces  Universal.lean::timedCut_Eval_reads: 83/88 = 94%
   Primitives.lean::splitCount_over  reproduces  Catalog.lean::f2_splitCount_over: 132/140 = 94%
   Catalog.lean::f2_splitSolve_of_body  reproduces  Primitives.lean::splitSolve_of_body: 886/940 = 94%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::rawStrip_rewind: 663/704 = 94%
   Primitives.lean::splitPrepareScan  reproduces  Catalog.lean::f2_splitPrepareScan: 97/103 = 94%
   Loop.lean::loopHost_round  reproduces  Catalog.lean::f2_loopHost_round: 1989/2114 = 94%
   Catalog.lean::f2_rawStrip_copy  reproduces  Primitives.lean::rawStrip_copy: 699/743 = 94%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Primitives.lean::splitPrepare_extra: 424/451 = 94%
   Catalog.lean::f2_loopDebit_success  reproduces  Loop.lean::loopDebit_success: 141/150 = 94%
   Catalog.lean::f2_splitRestore_first  reproduces  Primitives.lean::splitRestore_first: 608/647 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Universal.lean::timedCut_count_run  reproduces  UniversalInterpreter.lean::universal_count_run: 2197/2342 = 94%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 272/290 = 94%
   Primitives.lean::extract_block  reproduces  Catalog.lean::f2_extract_block: 633/675 = 94%
   Primitives.lean::incFixed_computes  reproduces  Primitives.lean::scanStep_right: 148/158 = 94%
   Catalog.lean::f2_splitFind_eq  reproduces  Primitives.lean::emitterSplit_find: 220/235 = 94%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_extract_rewind: 718/767 = 94%
   Catalog.lean::f2_exists_loopFind_space  reproduces  Loop.lean::exists_loopFindTM: 851/910 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::f2_splitSolve_source  reproduces  Primitives.lean::splitSolve_source: 397/425 = 93%
   Loop.lean::loopHost_replay  reproduces  Catalog.lean::f2_loopHost_replay: 1032/1105 = 93%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_setup: 533/571 = 93%
   Catalog.lean::f2_lenParse_run  reproduces  Primitives.lean::lenParse_run: 1533/1643 = 93%
   Primitives.lean::splitFind_eq  reproduces  Catalog.lean::f2_splitFind_eq: 221/237 = 93%
   Catalog.lean::f2_loopBodyPadded  reproduces  Loop.lean::loopBodyPadded: 137/147 = 93%
   Catalog.lean::f2_lenParse_first  reproduces  Primitives.lean::lenParse_first: 287/308 = 93%
   Loop.lean::loopHost_frame_replay  reproduces  Catalog.lean::f2_loopHost_frame_replay: 888/953 = 93%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_pair_get: 257/276 = 93%
   Catalog.lean::f2_splitCount_accept  reproduces  Primitives.lean::splitCount_accept: 266/286 = 93%
   Primitives.lean::pairDup_double  reproduces  Catalog.lean::f2_pairDup_double: 1127/1212 = 93%
   Universal.lean::timedCapture_transfer  reproduces  UniversalStartup.lean::universalCapture_transfer: 119/128 = 93%
   Primitives.lean::catalogPrefixTM_computes  reproduces  Catalog.lean::f2_catalogPrefixTM_computes: 369/397 = 93%
   Primitives.lean::splitEmit_suffix  reproduces  Catalog.lean::f2_splitEmit_suffix: 1056/1137 = 93%
   Universal.lean::timedSix  reproduces  Universal.lean::timedFive: 78/84 = 93%
   Primitives.lean::emitterSplit_find  reproduces  Catalog.lean::f2_splitFind_eq: 220/237 = 93%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Primitives.lean::splitRestore_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 799/861 = 93%
   Nondeterminism.lean::choiceVerifier_append  reproduces  Nondeterminism.lean::e3_choice_append: 192/207 = 93%
   Nondeterminism.lean::a2BorrowPos_le  reproduces  Catalog.lean::f2_loopBorrowPos_le: 89/96 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Loop.lean::loopReplay_step  reproduces  Catalog.lean::f2_loopReplay_step: 316/341 = 93%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_initial_skip: 934/1008 = 93%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 719/776 = 93%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 754/814 = 93%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::emitterToken_separator: 201/217 = 93%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_small_frame: 539/582 = 93%
   Loop.lean::loopHost_accept  reproduces  Catalog.lean::f2_loopHost_accept: 2127/2297 = 93%
   Primitives.lean::lenParse_block  reproduces  Catalog.lean::f2_lenParse_block: 700/756 = 93%
   Catalog.lean::f2_rawStrip_computes  reproduces  Primitives.lean::rawStrip_computes: 650/702 = 93%
   Primitives.lean::rawStrip_trim  reproduces  Catalog.lean::f2_rawStrip_trim: 575/621 = 93%
   Primitives.lean::scanCopy_finish  reproduces  Catalog.lean::f2_scanCopy_finish: 249/269 = 93%
   Primitives.lean::extract_finish  reproduces  Catalog.lean::f2_extract_finish: 595/643 = 93%
   Primitives.lean::extract_replay_finish  reproduces  Catalog.lean::f2_extract_replay_finish: 284/307 = 93%
   UniversalBlock.lean::universal_skip_unary  reproduces  Universal.lean::timedCut_skip_unary: 1160/1254 = 93%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Primitives.lean::catalogPoly_emit: 468/506 = 92%
   Catalog.lean::f2_pairExtract_computes  reproduces  Primitives.lean::pairExtract_computes: 443/479 = 92%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_pair_frame: 539/583 = 92%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::scanStep_right: 146/158 = 92%
   Nondeterminism.lean::e3_choice_no_split  reproduces  Nondeterminism.lean::choiceVerifier_no_split: 145/157 = 92%
   UniversalBlock.lean::universal_lookup_parts  reproduces  Universal.lean::timedCut_lookup_parts: 1305/1415 = 92%
   Universal.lean::timedCut_lookup_parts  reproduces  UniversalBlock.lean::universal_lookup_parts: 1305/1416 = 92%
   Primitives.lean::rawStrip_finish  reproduces  Catalog.lean::f2_rawStrip_finish: 270/293 = 92%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Loop.lean::loopHost_borrow_run: 489/531 = 92%
   Catalog.lean::f2_pairValid_run  reproduces  Primitives.lean::pairValid_run: 1083/1177 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   UniversalInterpreter.lean::universal_skip_fixed  reproduces  Universal.lean::timedCut_skip_fixed: 647/705 = 92%
   Catalog.lean::f2_lenSuffix_run  reproduces  Primitives.lean::lenSuffix_run: 1436/1566 = 92%
   UniversalInterpreter.lean::universal_table_rewind  reproduces  Universal.lean::timedCut_table_rewind: 637/695 = 92%
   Primitives.lean::emitterP2PairIndex  reproduces  Primitives.lean::emitterP2SmallIndex: 207/226 = 92%
   Primitives.lean::splitEmitCfg  reproduces  Catalog.lean::f2_splitEmitCfg: 97/106 = 92%
   Primitives.lean::catalogPoly_copy  reproduces  Catalog.lean::f2_catalogPoly_copy: 665/727 = 91%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 663/725 = 91%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Nondeterminism.lean::b2_compile  reproduces  Nondeterminism.lean::a2_compile: 924/1011 = 91%
   Primitives.lean::extract_first  reproduces  Catalog.lean::f2_extract_first: 274/300 = 91%
   Loop.lean::loopBodyPadded  reproduces  Catalog.lean::f2_loopBodyPadded: 137/150 = 91%
   Catalog.lean::f2_anyTrue_computes  reproduces  Primitives.lean::anyTrue_computes: 231/253 = 91%
   Catalog.lean::f2_incFixed_computes  reproduces  Primitives.lean::incFixed_computes: 2332/2555 = 91%
   Primitives.lean::rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_copy: 699/767 = 91%
   Primitives.lean::splitCount_accept  reproduces  Catalog.lean::f2_splitCount_accept: 266/292 = 91%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedCut_count_run: 2197/2414 = 91%
   UniversalBlock.lean::universal_prepare_next  reproduces  Universal.lean::timedCut_prepare_next: 1959/2154 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Catalog.lean::f2_splitPoly_loop_end  reproduces  Primitives.lean::splitPoly_loop_end: 639/703 = 91%
   Primitives.lean::splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 605/666 = 91%
   UniversalBlock.lean::universal_live_block  reproduces  Universal.lean::timedCut_live_block: 5237/5766 = 91%
   Catalog.lean::rewind_heads  reproduces  Primitives.lean::catalogRewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Primitives.lean::splitEmit_separator  reproduces  Catalog.lean::f2_splitEmit_separator: 730/804 = 91%
   Catalog.lean::f2_loopHost_round  reproduces  Loop.lean::loopHost_round: 1989/2194 = 91%
   Nondeterminism.lean::e3_split_none_iff  reproduces  Nondeterminism.lean::certificateSplit_none_iff: 155/171 = 91%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Loop.lean::loopFuelCaptured_frame: 1423/1570 = 91%
   Primitives.lean::splitRestore_first  reproduces  Catalog.lean::f2_splitRestore_first: 608/671 = 91%
   Universal.lean::timed_universal_concrete  reproduces  Universal.lean::timed_universal: 384/424 = 91%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanStep_right: 143/158 = 91%
   Universal.lean::timed_pair_get  reproduces  UniversalStartup.lean::universal_pair_get: 257/284 = 90%
   Catalog.lean::f2_catalogPrefixTM_emit  reproduces  Primitives.lean::catalogPrefixTM_emit: 321/355 = 90%
   Catalog.lean::f2_splitSource_constant  reproduces  Primitives.lean::splitSource_constant: 424/469 = 90%
   Loop.lean::loopDebit_success  reproduces  Catalog.lean::f2_loopDebit_success: 141/156 = 90%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_initial_skip: 911/1008 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   UHaltMachine.lean::primrec_replicate_numOfString  reproduces  MathlibBridge.lean::codePrimBit: 156/173 = 90%
   Nondeterminism.lean::contSplitWord  reproduces  Nondeterminism.lean::e3SplitWord: 64/71 = 90%
   CertShell.lean::certSplitWord  reproduces  Nondeterminism.lean::e3SplitWord: 64/71 = 90%
   Primitives.lean::computesFunInTime_pairEncodeFixed  reproduces  Catalog.lean::computesFunInTime_pairEncodeFixed_spaceUsed: 91/101 = 90%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_initial: 263/292 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Primitives.lean::mapParse_block  reproduces  Primitives.lean::mapParse_first: 244/271 = 90%
   Primitives.lean::lenParse_run  reproduces  Catalog.lean::f2_lenParse_run: 1533/1703 = 90%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_initial_skip: 873/970 = 90%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Loop.lean::loopHost_fuel_copy: 1319/1466 = 90%
   Primitives.lean::catalogPoly_start  reproduces  Catalog.lean::f2_catalogPoly_start: 833/926 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Loop.lean::loopHost_borrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 489/544 = 90%
   Primitives.lean::splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_extra: 424/472 = 90%
   Catalog.lean::f2_splitBody_round  reproduces  Primitives.lean::splitBody_round: 4481/4991 = 90%
   Primitives.lean::lenParse_first  reproduces  Catalog.lean::f2_lenParse_first: 287/320 = 90%
   Catalog.lean::f2_splitScratch_erase  reproduces  Primitives.lean::splitScratch_erase: 139/155 = 90%
   Nondeterminism.lean::cont_choiceVerifier_mem_P  reproduces  Nondeterminism.lean::e3_verifier_of_split: 929/1036 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Primitives.lean::splitSolve_source  reproduces  Catalog.lean::f2_splitSolve_source: 397/443 = 90%
   Primitives.lean::lenSuffix_run  reproduces  Primitives.lean::lenParse_first: 276/308 = 90%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Loop.lean::loopHost_anchor_return: 829/926 = 90%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Primitives.lean::splitBody_round  reproduces  Catalog.lean::f2_splitBody_round: 4481/5014 = 89%
   Catalog.lean::f2_exists_loopFind_space  reproduces  Loop.lean::exists_loopTM: 687/770 = 89%
   Primitives.lean::pairExtract_computes  reproduces  Catalog.lean::f2_pairExtract_computes: 443/497 = 89%
   Primitives.lean::catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_setup: 533/598 = 89%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopTM: 686/770 = 89%
   CodeFormat.lean::oneTapeFormat  reproduces  CodeFormat.lean::codeTable2Bits: 208/234 = 89%
   Catalog.lean::f2_loopReady  reproduces  Loop.lean::loopReady: 119/134 = 89%
   Primitives.lean::catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_emit: 468/527 = 89%
   Nondeterminism.lean::cont_parse_double  reproduces  Nondeterminism.lean::cont_parse_separator: 579/652 = 89%
   Catalog.lean::f2_splitRestore_append  reproduces  Primitives.lean::splitRestore_append: 1052/1185 = 89%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   MathlibBridge.lean::bridgeCfg_push  reproduces  MathlibBridge.lean::bridgeCfg_pop: 674/761 = 89%
   Universal.lean::timedCut_Interpreter_initialize  reproduces  UniversalInterpreter.lean::universalInterpreter_initialize: 1802/2036 = 89%
   Primitives.lean::lenSuffix_run  reproduces  Catalog.lean::f2_lenSuffix_run: 1436/1623 = 88%
   Nondeterminism.lean::a3n_eq_double  reproduces  Nondeterminism.lean::a3n_eq_separator: 1072/1212 = 88%
   Primitives.lean::rawStrip_computes  reproduces  Catalog.lean::f2_rawStrip_computes: 650/735 = 88%
   Catalog.lean::f2_pairDup_computes  reproduces  Primitives.lean::pairDup_computes: 1321/1494 = 88%
   Primitives.lean::splitCount_run  reproduces  Loop.lean::emCall_right_run: 152/172 = 88%
   Catalog.lean::f2_splitCount_run  reproduces  Loop.lean::emCall_right_run: 152/172 = 88%
   Loop.lean::loopDebit_value  reproduces  Catalog.lean::f2_loopDebit_value: 187/212 = 88%
   Primitives.lean::catalogBuffer_erase  reproduces  Loop.lean::emCall_erase_last: 118/134 = 88%
   Catalog.lean::f2_catalogBuffer_erase  reproduces  Loop.lean::emCall_erase_last: 118/134 = 88%
   Codes2Tape.lean::Code2TM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 206/234 = 88%
   Primitives.lean::pairValid_run  reproduces  Catalog.lean::f2_pairValid_run: 1083/1231 = 88%
   Catalog.lean::f2_scanStep_right  reproduces  Primitives.lean::scanStep_right: 139/158 = 88%
   Nondeterminism.lean::choiceCore_step  reproduces  Nondeterminism.lean::choiceCore_finish: 285/324 = 88%
   Primitives.lean::splitBody_prepare  reproduces  Primitives.lean::emitterP2_control: 73/83 = 88%
   Catalog.lean::f2_splitBody_prepare  reproduces  Primitives.lean::emitterP2_control: 73/83 = 88%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   UniversalStartup.lean::universalCapture_step  reproduces  Universal.lean::timedCapture_step: 1089/1241 = 88%
   Primitives.lean::catalogPrefixTM_emit  reproduces  Catalog.lean::f2_catalogPrefixTM_emit: 321/367 = 87%
   UniversalStartup.lean::universalCapture_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Universal.lean::timed_replay  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Universal.lean::timedCapture_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Loop.lean::emCall_right_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Catalog.lean::a2_mapSetup_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   SymbolLift.lean::Action.liftSymbols  reproduces  CounterLoop.lean::Action.mapWorkSymbols: 96/110 = 87%
   Primitives.lean::emitter_first_entry  reproduces  Primitives.lean::catalogFirstEntry: 327/375 = 87%
   Primitives.lean::emitter_first_entry  reproduces  Catalog.lean::f2_catalogFirstEntry: 327/375 = 87%
   Loop.lean::emCall_first_entry  reproduces  Primitives.lean::catalogFirstEntry: 327/375 = 87%
   Loop.lean::emCall_first_entry  reproduces  Catalog.lean::f2_catalogFirstEntry: 327/375 = 87%
   Primitives.lean::incFixed_computes  reproduces  Catalog.lean::f2_incFixed_computes: 2332/2675 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Primitives.lean::anyTrue_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 231/265 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   UniversalInterpreter.lean::universalInterpreter  reproduces  UniversalInterpreter.lean::universalSkipDone: 60/69 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Loop.lean::loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopFuelCaptured_frame: 1423/1639 = 87%
   UniversalStartup.lean::universalCapture_init  reproduces  Universal.lean::timedCapture_init: 276/318 = 87%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Nondeterminism.lean::b2_unary_run: 117/135 = 87%
   Catalog.lean::f2_loopBodySource_run  reproduces  Loop.lean::loopBodySource_run: 78/90 = 87%
   Catalog.lean::f2_loopHost_borrow_step  reproduces  Loop.lean::loopHost_borrow_step: 581/671 = 87%
   Primitives.lean::splitSource_constant  reproduces  Catalog.lean::f2_splitSource_constant: 424/490 = 87%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Primitives.lean::computesFunInTime_prepend: 122/141 = 87%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 661/764 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Nondeterminism.lean::e3SplitWord  reproduces  Nondeterminism.lean::contSplitWord: 64/74 = 86%
   Nondeterminism.lean::e3SplitWord  reproduces  CertShell.lean::certSplitWord: 64/74 = 86%
   Primitives.lean::splitPoly_loop_end  reproduces  Catalog.lean::f2_splitPoly_loop_end: 639/739 = 86%
   UniversalStartup.lean::universalCapture_run  reproduces  Universal.lean::timedCapture_run: 146/169 = 86%
   Universal.lean::timedCapture_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Loop.lean::loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 1319/1527 = 86%
   Primitives.lean::splitScratch_erase  reproduces  Catalog.lean::f2_splitScratch_erase: 139/161 = 86%
   CfgRecord.lean::recordStep_reject_run  reproduces  CfgRecord.lean::recordStep_empty_run: 467/541 = 86%
   Catalog.lean::f2_lenAction_apply  reproduces  Primitives.lean::lenAction_apply: 125/145 = 86%
   Loop.lean::loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_anchor_return: 829/963 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Catalog.lean::f2_strip_linear  reproduces  Primitives.lean::computesFunInTime_stripLast: 1616/1881 = 86%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_rewind: 1025/1195 = 86%
   Universal.lean::timedCut_live_block  reproduces  UniversalBlock.lean::universal_live_block: 5237/6108 = 86%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_pair_triple: 138/161 = 86%
   Primitives.lean::splitCount_run  reproduces  Universal.lean::timedFrame_run: 108/126 = 86%
   Catalog.lean::f2_splitCount_run  reproduces  Universal.lean::timedFrame_run: 108/126 = 86%
   Primitives.lean::emitterP2_update_right  reproduces  Primitives.lean::emitterP2_update_left: 542/633 = 86%
   UniversalInterpreter.lean::universalInterpreter_initialize  reproduces  Universal.lean::timedCut_Interpreter_initialize: 1802/2105 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_control: 71/83 = 86%
   Catalog.lean::f2_loopDebit_iterate_value  reproduces  Loop.lean::loopDebit_iterate_value: 248/290 = 86%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 661/773 = 86%
   Primitives.lean::splitStep_orbit  reproduces  Nondeterminism.lean::e3_step_orbit: 171/200 = 86%
   Catalog.lean::f2_splitStep_orbit  reproduces  Nondeterminism.lean::e3_step_orbit: 171/200 = 86%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedCapture_start: 434/508 = 85%
   CfgRecord.lean::recordStep_empty_run  reproduces  CfgRecord.lean::recordStep_reject_run: 467/547 = 85%
   Nondeterminism.lean::b2_ready_done  reproduces  Nondeterminism.lean::b2_ready_step: 539/632 = 85%
   Universal.lean::timedCapture_step  reproduces  Universal.lean::timedCapture_init: 271/318 = 85%
   CodeFormat.lean::oneTapeFormat  reproduces  CodeSimulator.lean::tableBitsK: 120/141 = 85%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::rawStrip_rewind: 599/704 = 85%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::rawStrip_rewind: 599/704 = 85%
   Nondeterminism.lean::e3_step_orbit  reproduces  Primitives.lean::splitStep_orbit: 171/201 = 85%
   Universal.lean::timedCapture_step  reproduces  UniversalStartup.lean::universalCapture_step: 1089/1281 = 85%
   Loop.lean::loopReady  reproduces  Catalog.lean::f2_loopReady: 119/140 = 85%
   Loop.lean::loopHost_fuel_setup  reproduces  Catalog.lean::f2_loopHost_fuel_setup: 782/921 = 85%
   Primitives.lean::splitSolve_of_body  reproduces  Nondeterminism.lean::e3_split_of_body: 796/938 = 85%
   CodeParser.lean::codeSkipAction  reproduces  CodeFormat.lean::codeSkipActionK: 106/125 = 85%
   Universal.lean::timedCapture_start  reproduces  UniversalStartup.lean::universalCapture_start: 434/512 = 85%
   Primitives.lean::scanStep_right  reproduces  Catalog.lean::f2_scanStep_right: 139/164 = 85%
   Nondeterminism.lean::e3_split_of_body  reproduces  Primitives.lean::splitSolve_of_body: 796/940 = 85%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanCopy_run: 408/482 = 85%
   Catalog.lean::f2_splitCount_apply  reproduces  Primitives.lean::splitCount_apply: 725/857 = 85%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_rewind_input: 1256/1488 = 84%
   Catalog.lean::f2_splitRestore_run  reproduces  Primitives.lean::splitRestore_run: 762/903 = 84%
   Catalog.lean::f2_loopHost_reject  reproduces  Loop.lean::loopHost_reject: 2023/2398 = 84%
   Primitives.lean::pairDup_computes  reproduces  Catalog.lean::f2_pairDup_computes: 1321/1566 = 84%
   Loop.lean::emCall_finalize_run  reproduces  Primitives.lean::emitterP2_control: 70/83 = 84%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Primitives.lean::splitRestore_append  reproduces  Catalog.lean::f2_splitRestore_append: 1052/1248 = 84%
   Catalog.lean::f2_anyTrue_run  reproduces  Primitives.lean::anyTrue_run: 669/795 = 84%
   Nondeterminism.lean::cont_split_answer  reproduces  Nondeterminism.lean::e3_split_answer: 659/784 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   ChoiceWords.lean::expCertificateLength_strictMono  reproduces  ChoiceWords.lean::certificateLength_strictMono: 83/99 = 84%
   Nondeterminism.lean::e3_step_orbit  reproduces  Catalog.lean::f2_splitStep_orbit: 171/204 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_splitBody_count  reproduces  Primitives.lean::splitBody_count: 483/577 = 84%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_bank_final: 3070/3669 = 84%
   Primitives.lean::emitterP2_update_left  reproduces  Primitives.lean::emitterP2_update_right: 542/648 = 84%
   Catalog.lean::f2_loopHost_fuel_setup  reproduces  Loop.lean::loopHost_fuel_setup: 782/935 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Primitives.lean::emitterSplit_result  reproduces  Primitives.lean::splitLoop_result: 193/231 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Loop.lean::loopHost_fuel_return: 982/1176 = 84%
   CounterLoop.lean::Action.mapWorkSymbols  reproduces  SymbolLift.lean::Action.liftSymbols: 96/115 = 83%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 630/755 = 83%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::f2_splitBody_rewind  reproduces  Primitives.lean::splitBody_rewind: 447/538 = 83%
   Nondeterminism.lean::cont_parse_separator  reproduces  Nondeterminism.lean::cont_parse_double: 579/697 = 83%
   Catalog.lean::f2_loopCopy_initial  reproduces  Loop.lean::loopCopy_initial: 78/94 = 83%
   Catalog.lean::f2_splitBody_prepare  reproduces  Primitives.lean::splitBody_prepare: 1263/1523 = 83%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 587/708 = 83%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Nondeterminism.lean::a3n_eq_double: 1072/1293 = 83%
   Universal.lean::timedCut_skip_unary  reproduces  UniversalInterpreter.lean::universal_initial_skip: 802/970 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Universal.lean::timedCapture_init  reproduces  UniversalStartup.lean::universalCapture_init: 276/334 = 83%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 599/725 = 83%
   Catalog.lean::f2_splitSolve_closed  reproduces  Primitives.lean::splitSolve_closed: 323/391 = 83%
   Loop.lean::loopHost_borrow_step  reproduces  Catalog.lean::f2_loopHost_borrow_step: 581/704 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Loop.lean::exists_emitCallTM  reproduces  Loop.lean::exists_installCallTM: 194/236 = 82%
   Catalog.lean::f2_lenSuffix_run  reproduces  Primitives.lean::lenParse_first: 253/308 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Loop.lean::loopHost_contracts  reproduces  Catalog.lean::f2_loopHost_contracts: 3565/4347 = 82%
   Loop.lean::emCall_prepare_run  reproduces  Primitives.lean::emitterP2_control: 68/83 = 82%
   Loop.lean::emCall_bank_step  reproduces  Primitives.lean::emitterP2_control: 68/83 = 82%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_reject_run: 448/547 = 82%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::computesFunInTime_pairConcat: 125/153 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Catalog.lean::f2_loopHost_prepare  reproduces  Loop.lean::loopHost_prepare: 1091/1338 = 82%
   Catalog.lean::f2_catalogPolyMove_apply  reproduces  Primitives.lean::catalogPolyMove_apply: 141/173 = 82%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 615/755 = 81%
   Primitives.lean::emitterSplit_result  reproduces  Catalog.lean::f2_splitLoop_result: 193/237 = 81%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Loop.lean::loopBodySource_run  reproduces  Catalog.lean::f2_loopBodySource_run: 78/96 = 81%
   Catalog.lean::f2_loopControl_apply  reproduces  Loop.lean::loopControl_apply: 643/792 = 81%
   Catalog.lean::f2_splitBody_restore  reproduces  Primitives.lean::splitBody_restore: 405/499 = 81%
   Loop.lean::loopHost_reject  reproduces  Catalog.lean::f2_loopHost_reject: 2023/2493 = 81%
   Primitives.lean::catalogFirstEntry  reproduces  Primitives.lean::emitter_first_entry: 327/403 = 81%
   Primitives.lean::catalogFirstEntry  reproduces  Loop.lean::emCall_first_entry: 327/403 = 81%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Primitives.lean::emitter_first_entry: 327/403 = 81%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Loop.lean::emCall_first_entry: 327/403 = 81%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 557/687 = 81%
   Nondeterminism.lean::e3_verifier_of_split  reproduces  Nondeterminism.lean::cont_choiceVerifier_mem_P: 929/1146 = 81%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopTM: 624/770 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Loop.lean::loopValue_bits  reproduces  Nondeterminism.lean::a2Value_bits: 106/131 = 81%
   Catalog.lean::f2_loopValue_bits  reproduces  Nondeterminism.lean::a2Value_bits: 106/131 = 81%
   Primitives.lean::anyTrue_run  reproduces  Catalog.lean::f2_anyTrue_run: 669/828 = 81%
   Catalog.lean::f2_loopBorrow_run  reproduces  Nondeterminism.lean::a2Borrow_run: 353/437 = 81%
   Primitives.lean::splitBody_count  reproduces  Catalog.lean::f2_splitBody_count: 483/598 = 81%
   Primitives.lean::splitLoop_result  reproduces  Primitives.lean::emitterSplit_result: 193/239 = 81%
   Catalog.lean::f2_splitLoop_result  reproduces  Primitives.lean::emitterSplit_result: 193/239 = 81%
   Primitives.lean::splitBody_rewind  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::splitBody_restore  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::emitterP2_prepare_first  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::emitterP2_erase_first  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Catalog.lean::f2_splitBody_rewind  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Catalog.lean::f2_splitBody_restore  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::computesFunInTime_pairSnd: 125/155 = 81%
   OracleNondeterministic.lean::OracleNDTM  reproduces  Oracle.lean::OracleTM: 141/175 = 81%
   Loop.lean::loopDebit_iterate_value  reproduces  Catalog.lean::f2_loopDebit_iterate_value: 248/308 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::extract_rewind: 599/746 = 80%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::extract_rewind: 599/746 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Universal.lean::timed_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Primitives.lean::splitCount_apply  reproduces  Catalog.lean::f2_splitCount_apply: 725/905 = 80%
   OracleSim.lean::oracleRestore_cell  reproduces  OracleSim.lean::oraclePrepare_zero: 112/140 = 80%
   Primitives.lean::splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_rewind: 447/559 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 630/790 = 80%
   OracleSim.lean::oracleMarkedCfg  reproduces  OracleSim.lean::oracleLocalCfg: 149/187 = 80%
   Primitives.lean::lenAction_apply  reproduces  Catalog.lean::f2_lenAction_apply: 125/157 = 80%
   UniversalBlock.lean::universal_skip_unary  reproduces  Universal.lean::timedCut_initial_skip: 802/1008 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Admin_apply: 210/264 = 80%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   Universal.lean::timedCut_Interpreter_first  reproduces  Universal.lean::timedCut_Admin_apply: 210/264 = 80%
   Loop.lean::emCall_right_scan  reproduces  Primitives.lean::emitterP2_control: 66/83 = 80%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Primitives.lean::emitterP2_control: 66/83 = 80%
   Primitives.lean::emitterAppend_run  reproduces  Catalog.lean::f2_scanCopy_run: 395/497 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Universal.lean::timedPrefix_complete  reproduces  Universal.lean::timedPrefix_penultimate: 318/401 = 79%
   Primitives.lean::extract_suffix  reproduces  Primitives.lean::extract_first: 226/285 = 79%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 615/776 = 79%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timed_clock_separator: 236/298 = 79%
   Primitives.lean::splitRestore_run  reproduces  Catalog.lean::f2_splitRestore_run: 762/963 = 79%
   Catalog.lean::f2_scanTrues_run  reproduces  Primitives.lean::scanStep_right: 125/158 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Primitives.lean::lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 253/320 = 79%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitPrepare_scan: 505/639 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_borrow_rewind: 932/1181 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_pairValid_block  reproduces  Primitives.lean::pairValid_block: 370/470 = 79%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_rewind_choices: 1256/1596 = 79%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 557/708 = 79%
   Primitives.lean::catalogPayload_computes  reproduces  Nondeterminism.lean::a3n_comp_at: 343/436 = 79%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Nondeterminism.lean::a2Value_bits  reproduces  Loop.lean::loopValue_bits: 106/135 = 79%
   Loop.lean::emCall_finish_final  reproduces  Loop.lean::emCall_finish_initial: 1279/1629 = 79%
   Nondeterminism.lean::e3_verifier_of_split  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::cont_choiceVerifier_mem_P  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::a2_exp_scheduler  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Primitives.lean::splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_prepare: 1263/1613 = 78%
   UHaltMachine.lean::primrec_replicate_numOfString  reproduces  MathlibBridge.lean::codePrimBitsNat: 101/129 = 78%
   UHaltMachine.lean::primrec_replicate_numOfString  reproduces  MathlibBridge.lean::bridgePrimNumber: 101/129 = 78%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Universal.lean::timedCaptureTM  reproduces  UniversalStartup.lean::universalCaptureTM: 291/372 = 78%
   Loop.lean::exists_installCallTM  reproduces  Loop.lean::exists_emitCallTM: 194/248 = 78%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 599/767 = 78%
   Nondeterminism.lean::b2_rewind_step  reproduces  Nondeterminism.lean::b2_copy_done: 303/388 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Nondeterminism.lean::b2_unary_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 117/150 = 78%
   Loop.lean::loopCopy_initial  reproduces  Catalog.lean::f2_loopCopy_initial: 78/100 = 78%
   Nondeterminism.lean::a2Borrow_step  reproduces  Catalog.lean::f2_loopBorrow_step: 328/421 = 78%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_reject_run: 426/547 = 78%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 615/790 = 78%
   Primitives.lean::splitSolve_closed  reproduces  Catalog.lean::f2_splitSolve_closed: 323/415 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 549/708 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Nondeterminism.lean::b2_copy_done  reproduces  Nondeterminism.lean::b2_rewind_step: 303/391 = 77%
   Primitives.lean::splitBody_restore  reproduces  Catalog.lean::f2_splitBody_restore: 405/523 = 77%
   MathlibBridge.lean::bridgeCfg_pop  reproduces  MathlibBridge.lean::bridgeCfg_push: 674/871 = 77%
   CodeFormat.lean::codeEraseActionK  reproduces  CodeFormat.lean::codeEraseWork: 167/216 = 77%
   Catalog.lean::f2_loopDebit_iterate_length  reproduces  Loop.lean::loopDebit_iterate_length: 68/88 = 77%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::scanStep_right: 122/158 = 77%
   Nondeterminism.lean::b2_host_bound  reproduces  Nondeterminism.lean::a2_host_bound: 381/494 = 77%
   Loop.lean::loopControl_apply  reproduces  Catalog.lean::f2_loopControl_apply: 643/834 = 77%
   Catalog.lean::f2_catalogPoly_advance  reproduces  Primitives.lean::catalogPoly_advance: 131/170 = 77%
   Nondeterminism.lean::b2_unary_run  reproduces  Universal.lean::timedFrame_run: 97/126 = 77%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_erase: 972/1264 = 77%
   Primitives.lean::splitLoop_bound  reproduces  Nondeterminism.lean::e3_loop_bound: 212/276 = 77%
   Nondeterminism.lean::e3_loop_bound  reproduces  Primitives.lean::splitLoop_bound: 212/276 = 77%
   Nondeterminism.lean::e3_loop_bound  reproduces  Catalog.lean::f2_splitLoop_bound: 212/276 = 77%
   Catalog.lean::f2_splitLoop_bound  reproduces  Nondeterminism.lean::e3_loop_bound: 212/276 = 77%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::a2_mapSetup_run: 125/163 = 77%
   Loop.lean::loopHost_halt_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 389/508 = 77%
   Nondeterminism.lean::b2_ready_run  reproduces  Nondeterminism.lean::b2_rewind_run: 196/256 = 77%
   Codes2Tape.lean::Code2TM.serialize  reproduces  UniversalInterpreter.lean::universalRecords: 160/209 = 77%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::emitterAppend_run: 408/533 = 77%
   Universal.lean::timedFive  reproduces  Universal.lean::timedSix: 78/102 = 76%
   Catalog.lean::f2_splitSolve_of_body  reproduces  Nondeterminism.lean::e3_split_of_body: 717/938 = 76%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Nondeterminism.lean::a2Buffer_write: 311/408 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Loop.lean::loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Primitives.lean::scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   Primitives.lean::catalogPolyMove_apply  reproduces  Catalog.lean::f2_catalogPolyMove_apply: 141/185 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Primitives.lean::emitterP2StateDecidableEq  reproduces  Primitives.lean::splitBodyStateDecidableEq: 408/537 = 76%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 587/773 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  UniversalStartup.lean::universalCapture_run: 128/169 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  Universal.lean::timedCapture_run: 128/169 = 76%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_initial: 221/292 = 76%
   Nondeterminism.lean::b2_guess_return  reproduces  Nondeterminism.lean::b2_initial: 221/292 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 615/814 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::computesFunInTime_pairFst: 117/155 = 75%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::computesFunInTime_pairSnd: 117/155 = 75%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Loop.lean::exists_loopTM  reproduces  Loop.lean::exists_loopFindTM: 686/910 = 75%
   MathlibBridge.lean::bridgeCfg_push_input  reproduces  MathlibBridge.lean::bridgeCfg_pop_emit: 195/259 = 75%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   Codes2Tape.lean::exists_uniformMachineCode2  reproduces  EXPCOM.lean::exists_uniformMachineCode: 322/428 = 75%
   Nondeterminism.lean::a2Value_bits  reproduces  Catalog.lean::f2_loopValue_bits: 106/141 = 75%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::extract_replay_finish: 224/298 = 75%
   EXPCOM.lean::exists_uniformMachineCode  reproduces  Codes2Tape.lean::exists_uniformMachineCode2: 322/429 = 75%
   Primitives.lean::splitSolve_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 672/896 = 75%
   Catalog.lean::f2_pairValid_computes  reproduces  Primitives.lean::pairValid_computes: 216/288 = 75%
   UniversalInterpreter.lean::universalRecords  reproduces  UniversalBlock.lean::universalActions: 105/140 = 75%
   UniversalInterpreter.lean::universalRecords  reproduces  Universal.lean::timedCut_Actions: 105/140 = 75%
   Codes2Tape.lean::Code2TM.serialize  reproduces  UniversalBlock.lean::universalActions: 105/140 = 75%
   Codes2Tape.lean::Code2TM.serialize  reproduces  Universal.lean::timedCut_Actions: 105/140 = 75%
   CodeFormat.lean::oneTapeFormat  reproduces  UniversalBlock.lean::universalActions: 105/140 = 75%
   CodeFormat.lean::oneTapeFormat  reproduces  Universal.lean::timedCut_Actions: 105/140 = 75%
   CodeFormat.lean::codeTable2Bits  reproduces  UniversalBlock.lean::universalActions: 105/140 = 75%
   CodeFormat.lean::codeTable2Bits  reproduces  Universal.lean::timedCut_Actions: 105/140 = 75%
   Primitives.lean::splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_extra: 338/451 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Primitives.lean::pairValid_block  reproduces  Catalog.lean::f2_pairValid_block: 370/494 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   CodeFormat.lean::parseFull  reproduces  CodeFormat.lean::scan: 151/202 = 75%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 879/1176 = 75%
   Loop.lean::loopDebit_iterate_length  reproduces  Catalog.lean::f2_loopDebit_iterate_length: 68/91 = 75%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 236/316 = 75%
   Nondeterminism.lean::e3_split_answer  reproduces  Nondeterminism.lean::cont_split_answer: 659/883 = 75%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopFindTM: 679/910 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::f2_loopBorrow_step  reproduces  Nondeterminism.lean::a2Borrow_step: 328/440 = 75%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timed_replay  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Oracle.lean::runFrom_plainEmptyOracle  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_ready_done: 539/724 = 74%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 879/1181 = 74%
   Nondeterminism.lean::a2Borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 353/476 = 74%
   Primitives.lean::emitterP2_body_length  reproduces  Primitives.lean::emitterP2_body_width: 493/665 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Universal.lean::timed_output_back  reproduces  Universal.lean::timed_clock_back: 401/541 = 74%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::emitterAppend_run: 395/533 = 74%
   Nondeterminism.lean::cont_core_run  reproduces  Seam.lean::seamRelease_step_right: 100/135 = 74%
   Nondeterminism.lean::cont_core_run  reproduces  Seam.lean::seamComp_step_right: 100/135 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Loop.lean::emCall_right_run  reproduces  UniversalStartup.lean::universalCapture_run: 125/169 = 74%
   Loop.lean::emCall_right_run  reproduces  Universal.lean::timedCapture_run: 125/169 = 74%
   Nondeterminism.lean::cont_core_run  reproduces  Catalog.lean::f2_splitEmbed_run: 139/188 = 74%
   UHaltMachine.lean::bits_foldr_bit_one  reproduces  MathlibBridge.lean::bridgeNumber_bits: 136/184 = 74%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_finish_final: 1279/1731 = 74%
   Universal.lean::timed_clock_back  reproduces  Universal.lean::timed_output_back: 401/543 = 74%
   Primitives.lean::extract_block  reproduces  Primitives.lean::extract_first: 210/285 = 74%
   Primitives.lean::splitLoop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 126/171 = 74%
   Catalog.lean::f2_splitLoop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 126/171 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Primitives.lean::emitterP2StateDecidableEq  reproduces  Catalog.lean::f2_splitBodyStateDecidableEq: 408/555 = 74%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Loop.lean::loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Oracle.lean::OracleTM  reproduces  OracleNondeterministic.lean::OracleNDTM: 141/192 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadWrite_sound: 143/195 = 73%
   Loop.lean::loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Loop.lean::loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::pairDupTM: 283/386 = 73%
   Primitives.lean::incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::pairDupTM: 283/386 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   OracleSim.lean::oracleRestore_cell  reproduces  OracleSim.lean::oraclePrepare_tail: 101/138 = 73%
   OracleSim.lean::oraclePrepare_zero  reproduces  OracleSim.lean::oraclePrepare_tail: 101/138 = 73%
   MathlibBridge.lean::CodeFormat.primrec_scan  reproduces  MathlibBridge.lean::codePrimSkipFin: 188/257 = 73%
   Primitives.lean::emitterP2_body_width  reproduces  Primitives.lean::emitterP2_body_length: 493/674 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   CfgRecord.lean::recordStep_map_snapshot  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 875/1198 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Nondeterminism.lean::a2Buffer_read: 65/89 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Loop.lean::loopBuffer_read: 65/89 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Universal.lean::timedFrame_run: 92/126 = 73%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalBlock.lean::universal_skip_unary: 873/1196 = 73%
   Primitives.lean::mapStart  reproduces  Primitives.lean::lenStart: 1210/1659 = 73%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Interpreter_first: 210/288 = 73%
   Universal.lean::timedCut_Admin_apply  reproduces  Universal.lean::timedCut_Interpreter_first: 210/288 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Universal.lean::timedCanon_complete  reproduces  UniversalStartup.lean::universalCanon_complete: 287/394 = 73%
   UniversalInterpreter.lean::universal_serialization_header  reproduces  UniversalBlock.lean::universal_serialization_actions: 589/809 = 73%
   UniversalInterpreter.lean::universal_serialization_header  reproduces  Universal.lean::timedCut_serialization_actions: 589/809 = 73%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 706/970 = 73%
   Loop.lean::loopHost_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1091/1499 = 73%
   Primitives.lean::splitCount_run  reproduces  UniversalStartup.lean::universalCapture_run: 123/169 = 73%
   Primitives.lean::splitCount_run  reproduces  Universal.lean::timedCapture_run: 123/169 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  UniversalStartup.lean::universalCapture_run: 123/169 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Universal.lean::timedCapture_run: 123/169 = 73%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 500/687 = 73%
   MathlibBridge.lean::bridgeNumber_bits  reproduces  UHaltMachine.lean::bits_foldr_bit_one: 136/187 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Universal.lean::timedCapture_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_skip_unary: 911/1254 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Universal.lean::timedCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Loop.lean::emCall_right_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   OracleSim.lean::oracleRestore_zero  reproduces  OracleSim.lean::oracleRestore_three: 74/102 = 73%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Primitives.lean::catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_emit: 366/506 = 72%
   Loop.lean::loopHost_start  reproduces  Catalog.lean::f2_loopHost_start: 209/289 = 72%
   Primitives.lean::splitRestore_append  reproduces  Primitives.lean::splitPrepare_extra: 326/451 = 72%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 496/687 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  UniversalStartup.lean::universalCapture_run: 122/169 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Universal.lean::timedCapture_run: 122/169 = 72%
   Universal.lean::timed_clock_get  reproduces  UniversalStartup.lean::universal_pair_get: 205/284 = 72%
   OracleSim.lean::oraclePrepare_tail  reproduces  OracleSim.lean::oraclePrepare_zero: 101/140 = 72%
   Nondeterminism.lean::a2Buffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Loop.lean::loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Primitives.lean::catalogPoly_advance  reproduces  Catalog.lean::f2_catalogPoly_advance: 131/182 = 72%
   Primitives.lean::emitterSplit_find  reproduces  Nondeterminism.lean::e3_find_eq: 123/171 = 72%
   Nondeterminism.lean::b2_ready_done  reproduces  Nondeterminism.lean::b2_initial: 210/292 = 72%
   Universal.lean::timedBorrow_length  reproduces  Universal.lean::timedBorrow_fold: 64/89 = 72%
   Primitives.lean::emitterP2_erase_back  reproduces  Nondeterminism.lean::a2Buffer_read: 64/89 = 72%
   Primitives.lean::emitterP2_erase_back  reproduces  Loop.lean::loopBuffer_read: 64/89 = 72%
   Primitives.lean::emitterP2_erase_back  reproduces  Catalog.lean::f2_loopBuffer_read: 64/89 = 72%
   Loop.lean::loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_return: 982/1366 = 72%
   Nondeterminism.lean::a2_load_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 549/764 = 72%
   Universal.lean::timedFrame_run  reproduces  Nondeterminism.lean::b2_unary_run: 97/135 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 706/987 = 72%
   OracleNondeterministic.lean::stepWith  reproduces  Oracle.lean::step: 118/165 = 72%
   Primitives.lean::emitterSplit_of_body  reproduces  Primitives.lean::splitSolve_of_body: 672/940 = 71%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_unary_copy: 704/985 = 71%
   Primitives.lean::splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Oracle.lean::runFrom_ofMultiTapeTM  reproduces  Catalog.lean::a2_mapSetup_heads: 70/98 = 71%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Loop.lean::loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Primitives.lean::splitFind_eq  reproduces  Nondeterminism.lean::e3_find_eq: 122/171 = 71%
   Catalog.lean::f2_splitFind_eq  reproduces  Nondeterminism.lean::e3_find_eq: 122/171 = 71%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_arg: 1025/1438 = 71%
   Catalog.lean::f2_loopReady_call  reproduces  Loop.lean::loopReady_call: 708/994 = 71%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 225/316 = 71%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 225/316 = 71%
   Nondeterminism.lean::choice_certificate_iff  reproduces  Nondeterminism.lean::e3_choice_certificate: 158/222 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_counterInc_bits  reproduces  Nondeterminism.lean::a2Value_bits: 93/131 = 71%
   Nondeterminism.lean::NP_eq_iUnion_NTIME  reproduces  Nondeterminism.lean::NEXP_eq_iUnion_NTIME: 66/93 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Loop.lean::emCall_right_run: 122/172 = 71%
   Catalog.lean::a2_mapVirtual_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 190/268 = 71%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 224/316 = 71%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 224/316 = 71%
   Nondeterminism.lean::e3_split_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 635/896 = 71%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState_fintype: 92/130 = 71%
   Primitives.lean::rawStripTM  reproduces  Loop.lean::loopReplayTM: 92/130 = 71%
   Primitives.lean::rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Loop.lean::loopReplayTM: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Primitives.lean::pairValid_computes  reproduces  Catalog.lean::f2_pairValid_computes: 216/306 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   Primitives.lean::lenStart  reproduces  Nondeterminism.lean::cont_pair_empty: 103/146 = 71%
   Catalog.lean::f2_lenStart  reproduces  Nondeterminism.lean::cont_pair_empty: 103/146 = 71%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::extract_replay_finish: 210/298 = 70%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Nondeterminism.lean::NEXP_eq_iUnion_NTIME  reproduces  Nondeterminism.lean::NP_eq_iUnion_NTIME: 66/94 = 70%
   Primitives.lean::splitRestoreTM  reproduces  Primitives.lean::splitPrepareTM: 280/399 = 70%
   Primitives.lean::splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Primitives.lean::splitPrepareTM: 280/399 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::extract_replay_finish: 209/298 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Loop.lean::loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 932/1329 = 70%
   Primitives.lean::splitRestoreScan  reproduces  Primitives.lean::splitPrepareScan: 68/97 = 70%
   Catalog.lean::f2_splitRestoreScan  reproduces  Primitives.lean::splitPrepareScan: 68/97 = 70%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadSign_sound: 159/227 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_reject_run: 383/547 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_inverse: 128/183 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_rewind: 835/1195 = 70%
   Nondeterminism.lean::a3n_scaled_envelope  reproduces  Nondeterminism.lean::a2_envelope: 535/766 = 70%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedCut_initial_skip: 704/1008 = 70%
   Loop.lean::loopDebit  reproduces  Nondeterminism.lean::a2Debit: 62/89 = 70%
   Catalog.lean::f2_loopDebit  reproduces  Nondeterminism.lean::a2Debit: 62/89 = 70%
   UniversalInterpreter.lean::universal_record_shape  reproduces  UniversalBlock.lean::universalActionBits_decode: 133/191 = 70%
   UniversalInterpreter.lean::universal_record_shape  reproduces  Universal.lean::timedCut_ActionBits_decode: 133/191 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   UniversalInterpreter.lean::universalEval_step  reproduces  Universal.lean::timedCut_Eval_step: 138/199 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::emitterToken_double: 543/785 = 69%
   CfgRecord.lean::recordStep_probe_run  reproduces  CfgRecord.lean::recordStep_read_run: 103/149 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Loop.lean::loopBody_step  reproduces  Loop.lean::loopBody_stop: 239/346 = 69%
   Nondeterminism.lean::cont_start_core  reproduces  Nondeterminism.lean::cont_write_apply: 221/320 = 69%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterP2_erase_scan: 218/316 = 69%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterP2_erase_scan: 218/316 = 69%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::scanStep_right: 109/158 = 69%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Primitives.lean::scanStep_right: 109/158 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Primitives.lean::emitterTokenTM  reproduces  Primitives.lean::pairDupTM: 266/386 = 69%
   Primitives.lean::emitterTokenTM  reproduces  Catalog.lean::f2_pairDupTM: 266/386 = 69%
   Primitives.lean::splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Primitives.lean::splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::f2_counterInc_bits  reproduces  Loop.lean::loopValue_bits: 93/135 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   Universal.lean::timed_replay  reproduces  Catalog.lean::a2_mapSetup_run: 112/163 = 69%
   Primitives.lean::emitterP2_erase_run  reproduces  Primitives.lean::emitterP2_erase_scan: 217/316 = 69%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::emitterP2_erase_scan: 217/316 = 69%
   Universal.lean::timedCut_Eval_step  reproduces  UniversalInterpreter.lean::universalEval_step: 138/201 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Loop.lean::loopDebit_value  reproduces  Nondeterminism.lean::a2Debit_value: 128/187 = 68%
   Catalog.lean::f2_loopDebit_value  reproduces  Nondeterminism.lean::a2Debit_value: 128/187 = 68%
   Universal.lean::timedBorrow_value  reproduces  Universal.lean::timedBorrow_underflow: 91/133 = 68%
   Loop.lean::loopHost_init  reproduces  Catalog.lean::f2_loopHost_init: 65/95 = 68%
   Primitives.lean::extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 210/307 = 68%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_empty_run: 370/541 = 68%
   Primitives.lean::rawStripTM  reproduces  Primitives.lean::emitterP2EraseTM: 188/275 = 68%
   Catalog.lean::f2_rawStripTM  reproduces  Primitives.lean::emitterP2EraseTM: 188/275 = 68%
   Nondeterminism.lean::cont_parse_run  reproduces  Nondeterminism.lean::a3n_eq_parse: 350/512 = 68%
   CodeParser.lean::codeReadSign_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 159/233 = 68%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_unary_copy: 673/987 = 68%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   UniversalStartup.lean::universalCapture_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Universal.lean::timed_replay  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Universal.lean::timedCapture_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Primitives.lean::splitCount_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Loop.lean::emCall_right_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Catalog.lean::f2_splitCount_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Catalog.lean::a2_mapSetup_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_unary_copy: 671/985 = 68%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::extract_replay_finish: 203/298 = 68%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::extract_replay_finish: 203/298 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_input_rewind  reproduces  Loop.lean::loopHost_input_rewind: 164/241 = 68%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairConcat: 104/153 = 68%
   Catalog.lean::f2_splitRestore_append  reproduces  Primitives.lean::splitPrepare_extra: 306/451 = 68%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_right_frame: 192/283 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedCut_live_before: 82/121 = 68%
   Universal.lean::timedCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Universal.lean::timedCapture_start  reproduces  Universal.lean::timedCut_live_before: 82/121 = 68%
   Catalog.lean::skipBackTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 969/1430 = 68%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairSnd: 105/155 = 68%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairFst: 105/155 = 68%
   RecordTable.lean::rt_find_scan_phase  reproduces  RecordTable.lean::rt_find_skip_phase: 344/508 = 68%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimUnary: 367/542 = 68%
   Primitives.lean::emitterSplit_of_body  reproduces  Nondeterminism.lean::e3_split_of_body: 635/938 = 68%
   Catalog.lean::f2_splitRestore_scan  reproduces  Primitives.lean::splitPrepare_scan: 432/639 = 68%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_arg: 972/1438 = 68%
   Primitives.lean::mapStart  reproduces  Catalog.lean::f2_lenStart: 1149/1701 = 68%
   CodeFormat.lean::codeSkipActionK  reproduces  CodeParser.lean::codeSkipAction: 106/157 = 68%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::a2_mapSetup_run: 110/163 = 67%
   Oracle.lean::step  reproduces  OracleNondeterministic.lean::stepWith: 118/175 = 67%
   CodeFormat.lean::codeTable2Bits  reproduces  CodeSimulator.lean::tableBitsK: 95/141 = 67%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_initial_skip: 678/1008 = 67%
   MathlibBridge.lean::codePrimSkipTable1  reproduces  MathlibBridge.lean::codePrimSkipTable2: 135/201 = 67%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::extract_replay: 390/581 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::extract_replay: 390/581 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::scanStep_right: 106/158 = 67%
   Universal.lean::timedCut_initial_skip  reproduces  UniversalBlock.lean::universal_skip_unary: 802/1196 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_initial_skip: 675/1008 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Loop.lean::loopHost_input_rewind  reproduces  Catalog.lean::f2_loopHost_input_rewind: 164/245 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::emitterAppend_run: 356/533 = 67%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_right_frame: 189/283 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Primitives.lean::emitterP2_body_prepare  reproduces  Primitives.lean::emitterP2_body_compare: 566/849 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Universal.lean::timed_clock_separator  reproduces  UniversalStartup.lean::universal_pair_separator: 138/207 = 67%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timed_pair_separator: 138/207 = 67%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_inverse: 122/183 = 67%
   Universal.lean::timed_replay  reproduces  Seam.lean::seamCompTM_runFrom_left: 112/168 = 67%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState_decidableEq: 92/138 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Universal.lean::timedBorrow_fold  reproduces  Universal.lean::timedBorrow_length: 64/96 = 67%
   Nondeterminism.lean::a2Debit  reproduces  Loop.lean::loopDebit: 62/93 = 67%
   Catalog.lean::f2_loopDebit  reproduces  Loop.lean::loopDebit: 62/93 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Nondeterminism.lean::b2_guess_run  reproduces  Nondeterminism.lean::cont_guess_run: 151/227 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::rawStrip_replay: 270/406 = 67%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::emitterTokenTM: 266/400 = 66%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::emitterTokenTM: 266/400 = 66%
   Primitives.lean::catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Primitives.lean::scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   CodeFormat.lean::codeTable2Bits  reproduces  Codes2Tape.lean::Code2TM.serialize: 206/310 = 66%
   Nondeterminism.lean::b2_rewind_run  reproduces  Nondeterminism.lean::b2_ready_run: 196/295 = 66%
   Primitives.lean::rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 390/587 = 66%
   Loop.lean::loopReady_call  reproduces  Catalog.lean::f2_loopReady_call: 708/1066 = 66%
   CodeParser.lean::codeBitsNat_bits  reproduces  Nondeterminism.lean::a2Value_bits: 87/131 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Universal.lean::timedCut_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 644/970 = 66%
   Loop.lean::emCall_track_action  reproduces  Universal.lean::timedCapture_init: 211/318 = 66%
   Universal.lean::timed_replay  reproduces  UniversalStartup.lean::universalCapture_run: 112/169 = 66%
   Universal.lean::timed_replay  reproduces  Universal.lean::timedCapture_run: 112/169 = 66%
   OracleSim.lean::oraclePrepare  reproduces  OracleSim.lean::oracleErase_step: 143/216 = 66%
   Catalog.lean::f2_splitSolve_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 593/896 = 66%
   Primitives.lean::rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 203/307 = 66%
   Nondeterminism.lean::e3_choice_certificate  reproduces  Nondeterminism.lean::choice_certificate_iff: 158/239 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_find_run: 448/678 = 66%
   Loop.lean::loop_run  reproduces  Catalog.lean::f2_loop_find_run: 448/678 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_erase: 835/1264 = 66%
   Primitives.lean::splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 68/103 = 66%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalInterpreter.lean::universal_initial_skip: 640/970 = 66%
   Primitives.lean::splitSolve_of_body  reproduces  Catalog.lean::f2_splitSolve_of_body: 886/1343 = 66%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_left_frame: 186/282 = 66%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::splitRewindTM: 122/185 = 66%
   Primitives.lean::incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_loopBody_step  reproduces  Loop.lean::loopBody_stop: 228/346 = 66%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 637/970 = 66%
   Catalog.lean::f2_loopHost_init  reproduces  Loop.lean::loopHost_init: 65/99 = 66%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_empty_run: 355/541 = 66%
   Primitives.lean::extract_run  reproduces  Primitives.lean::lenParse_run: 1077/1643 = 66%
   Universal.lean::timedFrame_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 110/168 = 65%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 500/764 = 65%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::extract_replay_finish: 195/298 = 65%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_unary_copy: 644/985 = 65%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::rawStrip_rewind: 460/704 = 65%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::rawStrip_rewind: 460/704 = 65%
   Universal.lean::timedPrefix_live  reproduces  UniversalStartup.lean::universal_live_before: 79/121 = 65%
   Universal.lean::timedPrefix_live  reproduces  Universal.lean::timedCut_live_before: 79/121 = 65%
   Catalog.lean::f2_catalogPair_inverse  reproduces  Nondeterminism.lean::a3n_pair_inverse: 220/337 = 65%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_empty_run: 353/541 = 65%
   Universal.lean::timedCut_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 644/987 = 65%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_pair: 152/233 = 65%
   Universal.lean::timed_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 135/207 = 65%
   Universal.lean::timed_pair_get  reproduces  Universal.lean::timed_pair_separator: 135/207 = 65%
   Nondeterminism.lean::b2_unary_step  reproduces  Seam.lean::seamRelease_step_right: 88/135 = 65%
   Nondeterminism.lean::b2_unary_step  reproduces  Seam.lean::seamComp_step_right: 88/135 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Universal.lean::timed_replay  reproduces  Loop.lean::emCall_right_run: 112/172 = 65%
   Universal.lean::timedFrame_run  reproduces  UniversalStartup.lean::universalCapture_run: 110/169 = 65%
   Universal.lean::timedFrame_run  reproduces  Universal.lean::timedCapture_run: 110/169 = 65%
   Primitives.lean::extract_suffix  reproduces  Primitives.lean::scanCopy_suffix: 553/850 = 65%
   Catalog.lean::f2_extract_suffix  reproduces  Primitives.lean::scanCopy_suffix: 553/850 = 65%
   Universal.lean::timedPrefix_code  reproduces  Universal.lean::timedPrefix_complete: 507/780 = 65%
   Nondeterminism.lean::a2Debit_value  reproduces  Loop.lean::loopDebit_value: 128/197 = 65%
   Loop.lean::loopBodyImage  reproduces  Loop.lean::emLoopCall: 87/134 = 65%
   Primitives.lean::lenStart  reproduces  Primitives.lean::mapStart: 1210/1864 = 65%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_left_frame: 183/282 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Primitives.lean::splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 432/666 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Primitives.lean::splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 306/472 = 65%
   Nondeterminism.lean::a2_host_bound  reproduces  Nondeterminism.lean::b2_host_bound: 381/588 = 65%
   Loop.lean::loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 228/352 = 65%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 171/264 = 65%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Admin_apply: 171/264 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_right_step: 134/207 = 65%
   Primitives.lean::scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 106/164 = 65%
   Catalog.lean::f2_loopCall_reframe  reproduces  Loop.lean::loopCall_reframe: 484/749 = 65%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::scanStep_right: 102/158 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   CodeFormat.lean::scan  reproduces  CodeFormat.lean::parseFull: 151/234 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_stamp: 450/698 = 64%
   CodeParser.lean::codeBitsNat_bits  reproduces  Loop.lean::loopValue_bits: 87/135 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Primitives.lean::splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_extract_run  reproduces  Primitives.lean::lenParse_run: 1057/1643 = 64%
   Primitives.lean::splitBody_rewind  reproduces  Primitives.lean::splitBody_restore: 321/499 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   CodeSimulator.lean::binaryGuard_escape  reproduces  CodeSimulator.lean::binaryGuard_done: 922/1434 = 64%
   Catalog.lean::f2_loopHost_release  reproduces  Loop.lean::loopHost_release: 524/815 = 64%
   Nondeterminism.lean::cont_split_length  reproduces  Nondeterminism.lean::e3_split_length: 90/140 = 64%
   Loop.lean::loopBody_run  reproduces  Universal.lean::timedFrame_run: 81/126 = 64%
   Catalog.lean::f2_loopBody_run  reproduces  Universal.lean::timedFrame_run: 81/126 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_pair_separator: 133/207 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 496/773 = 64%
   Primitives.lean::splitPrepareScan  reproduces  Primitives.lean::splitRestoreScan: 68/106 = 64%
   Catalog.lean::f2_splitPrepareScan  reproduces  Primitives.lean::splitRestoreScan: 68/106 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Primitives.lean::emitter_bits_injective  reproduces  Nondeterminism.lean::a2Value_bits: 84/131 = 64%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Nondeterminism.lean::a2Value_bits: 84/131 = 64%
   CodeFormat.lean::oneTapeFormat  reproduces  UniversalInterpreter.lean::universalRecords: 134/209 = 64%
   CodeFormat.lean::codeTable2Bits  reproduces  UniversalInterpreter.lean::universalRecords: 134/209 = 64%
   Primitives.lean::catalogPoly_emit  reproduces  Primitives.lean::catalogPoly_setup: 366/571 = 64%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_write_apply: 205/320 = 64%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_write_apply: 205/320 = 64%
   Nondeterminism.lean::e3ChoiceVerifier  reproduces  OracleNondeterministic.lean::AcceptsWithin: 71/111 = 64%
   Nondeterminism.lean::choiceVerifier  reproduces  OracleNondeterministic.lean::AcceptsWithin: 71/111 = 64%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_skip_unary: 802/1254 = 64%
   Universal.lean::timedFrame_run  reproduces  Loop.lean::emCall_right_run: 110/172 = 64%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedCut_initial_skip: 644/1008 = 64%
   ChoiceWords.lean::certificateLength_strictMono  reproduces  ChoiceWords.lean::expCertificateLength_strictMono: 83/130 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::rawStrip_replay: 259/406 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Primitives.lean::extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Primitives.lean::lenSuffix_run  reproduces  Primitives.lean::anyTrue_run: 506/795 = 64%
   Catalog.lean::f2_lenSuffix_run  reproduces  Primitives.lean::anyTrue_run: 506/795 = 64%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 168/264 = 64%
   UniversalBlock.lean::universal_apply_record  reproduces  Universal.lean::timedCut_Admin_apply: 168/264 = 64%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 168/264 = 64%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Admin_apply: 168/264 = 64%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timedClockPrefix_length: 89/140 = 64%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 195/307 = 64%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::rawStrip_rewind: 447/704 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::rawStrip_rewind: 447/704 = 63%
   Universal.lean::timed_output_step  reproduces  Universal.lean::timedClock_step: 158/249 = 63%
   Catalog.lean::a2_loop_prepare  reproduces  Loop.lean::loopHost_prepare: 849/1338 = 63%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Primitives.lean::emitterP2_body_compare  reproduces  Primitives.lean::emitterP2_body_prepare: 566/894 = 63%
   Catalog.lean::f2_incFixed_computes  reproduces  Primitives.lean::scanStep_right: 100/158 = 63%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::scanCopy_run: 305/482 = 63%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::splitPrepare_rewind: 477/755 = 63%
   Loop.lean::emCall_track_action  reproduces  UniversalStartup.lean::universalCapture_init: 211/334 = 63%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::extract_replay_finish: 188/298 = 63%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::extract_replay_finish: 188/298 = 63%
   Primitives.lean::pairExtractTM  reproduces  Loop.lean::loopReplayTM: 82/130 = 63%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Nondeterminism.lean::a3n_unpad_EXP  reproduces  ChoiceWords.lean::expCertificateLength_strictMono: 82/130 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Loop.lean::loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::splitPrepare_rewind: 476/755 = 63%
   Nondeterminism.lean::a3n_eq_scan  reproduces  Primitives.lean::emitterP2_erase_scan: 199/316 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 259/412 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::rawStrip_rewind: 442/704 = 63%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::rawStrip_rewind: 442/704 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::splitRewindTM: 116/185 = 63%
   Primitives.lean::pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::splitRewindTM: 116/185 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timed_pair_get: 173/276 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Nondeterminism.lean::a2Debit  reproduces  Catalog.lean::f2_loopDebit: 62/99 = 63%
   Loop.lean::loopDebit  reproduces  Catalog.lean::f2_loopDebit: 62/99 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timed_clock_get: 236/377 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::rawStrip_replay: 254/406 = 63%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::rawStrip_replay: 254/406 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Universal.lean::timedCanon_run  reproduces  UniversalStartup.lean::universalCanon_run: 187/300 = 62%
   Loop.lean::loopHost_borrow_run  reproduces  Nondeterminism.lean::a2Borrow_run: 272/437 = 62%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Nondeterminism.lean::a2Borrow_run: 272/437 = 62%
   Primitives.lean::emitter_bits_injective  reproduces  Loop.lean::loopValue_bits: 84/135 = 62%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Loop.lean::loopValue_bits: 84/135 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Primitives.lean::pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 102/164 = 62%
   Loop.lean::loopBodyDispatch  reproduces  Loop.lean::loopBodyImage: 118/190 = 62%
   Loop.lean::loopBody_stop  reproduces  Universal.lean::timedCapture_transfer: 77/124 = 62%
   Catalog.lean::f2_loopBody_stop  reproduces  Universal.lean::timedCapture_transfer: 77/124 = 62%
   Primitives.lean::extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1057/1703 = 62%
   UniversalBlock.lean::universal_skip_unary  reproduces  Universal.lean::timedCut_unary_copy: 611/985 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   CodeFormat.lean::oneTapeFormat  reproduces  Codes2Tape.lean::Code2TM.serialize: 192/310 = 62%
   Universal.lean::timedCut_skip_unary  reproduces  UniversalInterpreter.lean::universal_unary_copy: 611/987 = 62%
   Primitives.lean::lenCfg  reproduces  Primitives.lean::mapCfg: 99/160 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Primitives.lean::pairExtractTM  reproduces  Primitives.lean::rawStripTM: 285/461 = 62%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Primitives.lean::rawStripTM: 285/461 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::extract_rewind: 461/746 = 62%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::extract_rewind: 461/746 = 62%
   CodeParser.lean::codeBitsNat_bits  reproduces  Catalog.lean::f2_loopValue_bits: 87/141 = 62%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 447/725 = 62%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 254/412 = 62%
   Primitives.lean::mapStart  reproduces  Nondeterminism.lean::cont_pair_empty: 90/146 = 62%
   Catalog.lean::f2_lenStart  reproduces  Primitives.lean::mapStart: 1149/1864 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   CodeFormat.lean::actionBits₂  reproduces  CodeFormat.lean::actionBitsK: 93/151 = 62%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Catalog.lean::f2_splitPrepare_rewind: 477/776 = 61%
   Nondeterminism.lean::b2_copy_step  reproduces  Nondeterminism.lean::a2_copy_step: 325/529 = 61%
   Catalog.lean::f2_extract_suffix  reproduces  Primitives.lean::extract_first: 175/285 = 61%
   CodeParser.lean::codeReadWrite_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 143/233 = 61%
   Primitives.lean::lenParse_block  reproduces  Primitives.lean::lenParse_first: 189/308 = 61%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Catalog.lean::f2_splitPrepare_rewind: 476/776 = 61%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_payload_scan: 422/688 = 61%
   UniversalStartup.lean::universalCapture_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Universal.lean::timed_replay  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Universal.lean::timedFrame_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Universal.lean::timedCapture_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Primitives.lean::splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Loop.lean::emCall_right_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::a2_mapSetup_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Loop.lean::loopFuel_init  reproduces  Universal.lean::timedCapture_init: 195/318 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Universal.lean::timedCapture_init: 195/318 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 188/307 = 61%
   Primitives.lean::lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 506/828 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Loop.lean::emCall_clear_scan  reproduces  Primitives.lean::emitterP2_erase_scan: 193/316 = 61%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 461/755 = 61%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 461/755 = 61%
   Primitives.lean::incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 100/164 = 61%
   Primitives.lean::emitterAppend_run  reproduces  Catalog.lean::f2_scanStep_right: 100/164 = 61%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Nondeterminism.lean::a3n_pair_inverse  reproduces  Catalog.lean::f2_catalogPair_inverse: 220/361 = 61%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 460/755 = 61%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 460/755 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Primitives.lean::splitPrepare_scan  reproduces  Primitives.lean::splitRestore_scan: 505/831 = 61%
   Primitives.lean::splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 68/112 = 61%
   OracleNondeterministic.lean::runWith_headBlank  reproduces  OracleNondeterministic.lean::OracleNDTM.stepWith_eq_of_ne_qQuery: 83/137 = 61%
   Loop.lean::loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 288/476 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_erase: 764/1264 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_rewind: 722/1195 = 60%
   Nondeterminism.lean::a2Debit_value  reproduces  Catalog.lean::f2_loopDebit_value: 128/212 = 60%
   Primitives.lean::mapBuffer_rewind  reproduces  Primitives.lean::mapPayload_replay: 372/617 = 60%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Nondeterminism.lean::cont_core_run: 170/282 = 60%
   Primitives.lean::mapParse_first  reproduces  Primitives.lean::mapParse_block: 244/405 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::rawStrip_erase: 213/354 = 60%
   OracleSim.lean::oracleChoiceAction_apply  reproduces  OracleSim.lean::oracleChoice_initial: 145/241 = 60%
   Loop.lean::loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Catalog.lean::f2_loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   RecordTable.lean::rt_find_skip_phase  reproduces  RecordTable.lean::rt_find_scan_phase: 344/572 = 60%
   Catalog.lean::f2_loopHost_borrow  reproduces  Loop.lean::loopHost_borrow: 258/429 = 60%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 461/767 = 60%
   Loop.lean::loopHost_release  reproduces  Catalog.lean::f2_loopHost_release: 524/872 = 60%
   Catalog.lean::seekEndTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 859/1430 = 60%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::extract_rewind: 448/746 = 60%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::extract_rewind: 448/746 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Nondeterminism.lean::cont_mask_count  reproduces  Nondeterminism.lean::b2_unary_run: 81/135 = 60%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::scanCopy_run: 289/482 = 60%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::scanCopy_finish: 154/257 = 60%
   UniversalStartup.lean::universalCaptureTM  reproduces  Universal.lean::timedCaptureTM: 291/486 = 60%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitCount_over: 82/137 = 60%
   Catalog.lean::f2_splitRestore_scan  reproduces  Primitives.lean::splitCount_over: 82/137 = 60%
   Loop.lean::loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_reframe: 484/809 = 60%
   Primitives.lean::emitter_compare_scan  reproduces  Primitives.lean::emitterP2_erase_scan: 189/316 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::splitPrepare_scan: 382/639 = 60%
   Loop.lean::emCall_track_initial  reproduces  Universal.lean::timedCapture_init: 190/318 = 60%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopCfgTM: 95/159 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::incFixedTM: 283/474 = 60%
   Primitives.lean::pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::incFixedTM: 283/474 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Loop.lean::loopCall  reproduces  Loop.lean::emLoopCall: 80/134 = 60%
   Primitives.lean::splitBody_restore  reproduces  Primitives.lean::splitBody_rewind: 321/538 = 60%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::emitterAppend_run: 318/533 = 60%
   Catalog.lean::f2_extract_block  reproduces  Primitives.lean::extract_first: 170/285 = 60%
   MathlibBridge.lean::bridgeCfg_pop_emit  reproduces  MathlibBridge.lean::bridgeCfg_push_input: 195/327 = 60%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_clear_heads: 124/208 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Universal.lean::timedCut_read_fixed  reproduces  Universal.lean::timedCut_skip_fixed: 420/705 = 60%
   Primitives.lean::emitter_bits_injective  reproduces  Catalog.lean::f2_loopValue_bits: 84/141 = 60%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Catalog.lean::f2_loopValue_bits: 84/141 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipState: 215/361 = 60%
   Catalog.lean::catalog_redirect_loop  reproduces  Universal.lean::timedFrame_run: 75/126 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   CfgRecord.lean::recordStep_read_prefix  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 712/1198 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeParser.lean::codeReadSymbols_sound: 142/239 = 59%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 461/776 = 59%
   Universal.lean::timedClock_step  reproduces  Universal.lean::timed_output_step: 158/266 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::extract_rewind: 443/746 = 59%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::extract_rewind: 443/746 = 59%
   Catalog.lean::f2_lenCfg  reproduces  Primitives.lean::mapCfg: 95/160 = 59%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopTM: 457/770 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamRelease_step_right: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamComp_step_right: 80/135 = 59%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_pair: 138/233 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   CfgRecord.lean::recordStep_restore_digits  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   CfgRecord.lean::recordStep_prepare_native  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::splitRestore_rewind: 467/790 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   CodeParser.lean::codeReadWrite  reproduces  CodeParser.lean::codeReadOutput: 65/110 = 59%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::splitRestore_rewind: 466/790 = 59%
   Catalog.lean::f2_counter_rewind  reproduces  Primitives.lean::emitterToken_separator: 128/217 = 59%
   Catalog.lean::f2_loopCall  reproduces  Loop.lean::emLoopCall: 79/134 = 59%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::emitterP2_erase_scan: 186/316 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::emitterP2_erase_scan: 186/316 = 59%
   Primitives.lean::catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Primitives.lean::splitEmbed_cut  reproduces  Universal.lean::timedFrame_run: 74/126 = 59%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Universal.lean::timedFrame_run: 74/126 = 59%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Universal.lean::timedFrame_run: 74/126 = 59%
   UniversalBlock.lean::universal_apply_record  reproduces  Universal.lean::timedCut_Interpreter_first: 169/288 = 59%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Interpreter_first: 169/288 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 448/764 = 59%
   Primitives.lean::splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   Primitives.lean::catalogPoly_setup  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   Primitives.lean::catalogPoly_emit  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 447/764 = 59%
   Nondeterminism.lean::NP_subset_iUnion_NTIME  reproduces  Nondeterminism.lean::NEXP_subset_iUnion_NTIME: 62/106 = 58%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_fintype: 76/130 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  Universal.lean::timed_pair_separator: 121/207 = 58%
   UniversalStartup.lean::universalCanon_run  reproduces  Universal.lean::timedCanon_run: 187/320 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 448/767 = 58%
   Loop.lean::loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Catalog.lean::f2_loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::rawStrip_replay: 237/406 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::rawStrip_replay: 237/406 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Primitives.lean::extract_suffix  reproduces  Catalog.lean::f2_extract_first: 175/300 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Interpreter_first: 168/288 = 58%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 169/290 = 58%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 169/290 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 184/316 = 58%
   Nondeterminism.lean::a2_load_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 184/316 = 58%
   Primitives.lean::pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 289/497 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Primitives.lean::lenParse_run  reproduces  Primitives.lean::extract_run: 1077/1854 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Primitives.lean::rawStrip_erase  reproduces  Universal.lean::timedCapture_transfer: 72/124 = 58%
   Catalog.lean::f2_rawStrip_erase  reproduces  Universal.lean::timedCapture_transfer: 72/124 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Loop.lean::loopHost_borrow  reproduces  Catalog.lean::f2_loopHost_borrow: 258/445 = 58%
   Primitives.lean::extract_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 448/773 = 58%
   Catalog.lean::f2_extract_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 448/773 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Oracle.lean::runFrom_plainEmptyOracle  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   Embed.lean::embedThroughHalt  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   Catalog.lean::a2_mapSetup_heads  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 168/290 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopCfgTM: 92/159 = 58%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_empty_run: 313/541 = 58%
   Loop.lean::emCall_clear_left  reproduces  Loop.lean::emCall_clear_scan: 369/638 = 58%
   Primitives.lean::rawStrip_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 447/773 = 58%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 447/773 = 58%
   Loop.lean::loopBody_run  reproduces  Nondeterminism.lean::b2_unary_run: 78/135 = 58%
   Catalog.lean::f2_loopBody_run  reproduces  Nondeterminism.lean::b2_unary_run: 78/135 = 58%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 443/767 = 58%
   Catalog.lean::seekStartTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 825/1430 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Primitives.lean::incFixed_computes  reproduces  Primitives.lean::emitterToken_separator: 125/217 = 58%
   Catalog.lean::f2_incFixed_computes  reproduces  Primitives.lean::emitterToken_separator: 125/217 = 58%
   Nondeterminism.lean::a2_envelope  reproduces  Nondeterminism.lean::a3n_scaled_envelope: 535/929 = 58%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 237/412 = 58%
   Loop.lean::emCallTripleEmbedding  reproduces  Loop.lean::emCallPairEmbedding: 69/120 = 57%
   Loop.lean::emCall_track_stamp  reproduces  Loop.lean::emCall_track_initial: 398/693 = 57%
   CfgRecord.lean::recordStep_clear_snapshot  reproduces  CfgRecord.lean::recordStep_map_snapshot: 875/1525 = 57%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Catalog.lean::f2_splitRestore_rewind: 467/814 = 57%
   Nondeterminism.lean::cont_split_answer  reproduces  Nondeterminism.lean::cont_split_length: 110/192 = 57%
   UniversalInterpreter.lean::universalRecords  reproduces  CodeFormat.lean::codeTable2Bits: 134/234 = 57%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Catalog.lean::f2_splitRestore_rewind: 466/814 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Universal.lean::timed_universal  reproduces  Universal.lean::timed_universal_concrete: 384/671 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Nondeterminism.lean::choiceCore_step  reproduces  Nondeterminism.lean::cont_write_apply: 183/320 = 57%
   CodeParser.lean::codeReadState_sound  reproduces  CodeParser.lean::codeReadUnary_sound: 223/390 = 57%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::rawStrip_replay: 232/406 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::rawStrip_replay: 232/406 = 57%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_pair_triple: 92/161 = 57%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Catalog.lean::a2_mapVirtual_run  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Loop.lean::loop_output_length_le: 145/254 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Loop.lean::emCall_track_initial  reproduces  Loop.lean::emCall_track_stamp: 398/698 = 57%
   Catalog.lean::f2_lenParse_run  reproduces  Primitives.lean::extract_run: 1057/1854 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_arg: 819/1438 = 57%
   Loop.lean::emCall_track_initial  reproduces  UniversalStartup.lean::universalCapture_init: 190/334 = 57%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalInterpreter.lean::universal_unary_copy: 560/987 = 57%
   Loop.lean::emLoopCall  reproduces  Loop.lean::loopCall: 80/141 = 57%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_copyback_run: 1173/2070 = 57%
   Primitives.lean::extract_block  reproduces  Catalog.lean::f2_extract_first: 170/300 = 57%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_unary_copy: 558/985 = 57%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 666/1176 = 57%
   CfgRecord.lean::RecordEqIndex  reproduces  CfgRecord.lean::RecordTestIndex: 73/129 = 57%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 427/755 = 57%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_skip_unary: 709/1254 = 57%
   OracleSim.lean::oracleMarkedCfg  reproduces  OracleSim.lean::oracleBackCfg: 91/161 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   MathlibBridge.lean::bridge_back  reproduces  MathlibBridge.lean::bridge_scan: 422/747 = 56%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Loop.lean::emCallPairIndex  reproduces  Loop.lean::emCallPairSelect: 61/108 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Nondeterminism.lean::b2_unary_run  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   UHaltMachine.lean::bits_foldr_bit_one  reproduces  UHaltMachine.lean::foldr_bit_one_pos: 62/110 = 56%
   UniversalInterpreter.lean::universal_state_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedPrefix_clock_end  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedPrefix_clock  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedCut_state_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Nondeterminism.lean::a2_load_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   MathlibBridge.lean::bridge_seed  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   MathlibBridge.lean::bridge_back  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Loop.lean::emCall_track_run  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Primitives.lean::emitterP2_prepare_candidate  reproduces  Primitives.lean::emitterP2_erase_scan: 178/316 = 56%
   Loop.lean::loop_rewind_bounded  reproduces  Primitives.lean::catalogRewind: 245/435 = 56%
   Loop.lean::loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Primitives.lean::catalogRewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalBlock.lean::universal_skip_unary: 673/1196 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Universal.lean::timedCanon_start  reproduces  UniversalStartup.lean::universalCanon_start: 189/336 = 56%
   Primitives.lean::rawStrip_erase  reproduces  UniversalStartup.lean::universalCapture_transfer: 72/128 = 56%
   Catalog.lean::f2_rawStrip_erase  reproduces  UniversalStartup.lean::universalCapture_transfer: 72/128 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::emitterToken_separator: 122/217 = 56%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Primitives.lean::emitterToken_separator: 122/217 = 56%
   Primitives.lean::splitBodyStateDecidableEq  reproduces  Primitives.lean::emitterP2StateDecidableEq: 408/726 = 56%
   Catalog.lean::f2_splitBodyStateDecidableEq  reproduces  Primitives.lean::emitterP2StateDecidableEq: 408/726 = 56%
   CodeSimulator.lean::canonHeader_length  reproduces  CodeSimulator.lean::canonHeaderOK_iff: 82/146 = 56%
   Nondeterminism.lean::e3_shift_scan  reproduces  Catalog.lean::f2_idTM_run: 434/773 = 56%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_transfer: 819/1459 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::splitRestore_rewind: 443/790 = 56%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::splitRestore_rewind: 443/790 = 56%
   RecordTable.lean::joinFields_cfgRecord_length  reproduces  RecordTable.lean::cfgRecord_init: 111/198 = 56%
   UniversalInterpreter.lean::universalRecords  reproduces  CodeSimulator.lean::tableBitsK: 79/141 = 56%
   Codes2Tape.lean::Code2TM.serialize  reproduces  CodeSimulator.lean::tableBitsK: 79/141 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Primitives.lean::computesFunInTime_prepend  reproduces  Catalog.lean::computesFunInTime_prepend_spaceUsed: 122/218 = 56%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::splitRestore_rewind: 442/790 = 56%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::splitRestore_rewind: 442/790 = 56%
   Catalog.lean::catalogCopyF  reproduces  Scan.lean::scanWriteCfg: 113/202 = 56%
   Primitives.lean::mapCfg  reproduces  Primitives.lean::lenCfg: 99/177 = 56%
   Loop.lean::emCall_exit_fixed  reproduces  OracleSim.lean::oracleBankCfg_eq: 203/363 = 56%
   Nondeterminism.lean::a3n_eq_parse  reproduces  Nondeterminism.lean::cont_parse_run: 350/626 = 56%
   Catalog.lean::f2_lenParse_block  reproduces  Primitives.lean::lenParse_first: 172/308 = 56%
   Catalog.lean::a2_map_parse  reproduces  Primitives.lean::extract_run: 1035/1854 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   OracleSim.lean::oracleChoice_initial  reproduces  OracleSim.lean::oracleChoiceAction_apply: 145/260 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timedClockPrefix_length: 78/140 = 56%
   Primitives.lean::emitterToken_double  reproduces  Primitives.lean::scanStep_right: 88/158 = 56%
   Primitives.lean::extract_replay_finish  reproduces  Universal.lean::timedCapture_transfer: 69/124 = 56%
   Catalog.lean::f2_extract_replay_finish  reproduces  Universal.lean::timedCapture_transfer: 69/124 = 56%
   UniversalStartup.lean::universalPrefix_start  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   UniversalStartup.lean::universalPrefix_bits  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedPrefix_complete  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedPrefix_code  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Seam.lean::seamRelease_run_pos  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::splitEmit_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::pairDup_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::pairDup_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::incFixed_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::emitterP2_prepare_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Oracle.lean::runFrom_ofMultiTapeTM  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   MathlibBridge.lean::bridge_emit  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_pairDup_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_pairDup_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_incFixed_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::pairDup_double: 653/1176 = 56%
   Catalog.lean::f2_idTM_run  reproduces  Nondeterminism.lean::e3_shift_scan: 434/782 = 55%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_finish_initial: 904/1629 = 55%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Loop.lean::loopHost_halt_return: 389/701 = 55%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::pairDup_double: 652/1176 = 55%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 322/581 = 55%
   Primitives.lean::emitterP2_erase_scan  reproduces  Primitives.lean::rawStrip_replay: 225/406 = 55%
   Primitives.lean::lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1057/1908 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 175/316 = 55%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_skip_unary: 694/1254 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 479/866 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 479/866 = 55%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::scanCopy_finish: 142/257 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 477/866 = 55%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 477/866 = 55%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_decidableEq: 76/138 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 427/776 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::emitterTokenTM: 220/400 = 55%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::emitterTokenTM: 220/400 = 55%
   UniversalStartup.lean::universal_pair_length  reproduces  Universal.lean::timedClockPrefix_length: 77/140 = 55%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 476/866 = 55%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 476/866 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   CfgRecord.lean::RecordTestIndex  reproduces  CfgRecord.lean::RecordEqIndex: 73/133 = 55%
   Loop.lean::emLoopCall  reproduces  Catalog.lean::f2_loopCall: 79/144 = 55%
   Scan.lean::scanWriteCfg  reproduces  Catalog.lean::catalogCopyF: 113/206 = 55%
   Primitives.lean::splitEmbed_cut  reproduces  Primitives.lean::emitter_first_entry: 221/403 = 55%
   Primitives.lean::splitEmbed_cut  reproduces  Loop.lean::emCall_first_entry: 221/403 = 55%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Primitives.lean::emitter_first_entry: 221/403 = 55%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Loop.lean::emCall_first_entry: 221/403 = 55%
   Primitives.lean::rawStrip_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Primitives.lean::rawStrip_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Primitives.lean::extract_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Primitives.lean::extract_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_rawStrip_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   UniversalStartup.lean::universalCanon_start  reproduces  Universal.lean::timedCanon_start: 189/345 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Nondeterminism.lean::b2_unary_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   UniversalBlock.lean::universal_skip_groups  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   UniversalBlock.lean::universal_prepare_next  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   UniversalBlock.lean::universal_live_block  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Universal.lean::timedCut_skip_groups  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Nondeterminism.lean::cont_rewind_input  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Primitives.lean::emitter_compare_run  reproduces  Primitives.lean::emitterP2_erase_scan: 173/316 = 55%
   Loop.lean::loopHost_body_run  reproduces  Catalog.lean::f2_loopHost_body_capture: 64/117 = 55%
   Loop.lean::loopBodyCfg  reproduces  Oracle.lean::Cfg.embedOracle: 100/183 = 55%
   Catalog.lean::f2_loopBodyCfg  reproduces  Oracle.lean::Cfg.embedOracle: 100/183 = 55%
   Primitives.lean::emitterP2_erase_scan  reproduces  Catalog.lean::f2_rawStrip_replay: 225/412 = 55%
   Loop.lean::loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 203/372 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Primitives.lean::extract_run  reproduces  Primitives.lean::pairValid_run: 641/1177 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  UniversalStartup.lean::universalCapture_run: 92/169 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Universal.lean::timedCapture_run: 92/169 = 54%
   Nondeterminism.lean::b2_unary_run  reproduces  UniversalStartup.lean::universalCapture_run: 92/169 = 54%
   Nondeterminism.lean::b2_unary_run  reproduces  Universal.lean::timedCapture_run: 92/169 = 54%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalBlock.lean::universal_skip_unary: 651/1196 = 54%
   Primitives.lean::catalogPayload_length  reproduces  Catalog.lean::f2_first_length: 86/158 = 54%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 443/814 = 54%
   Primitives.lean::extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Nondeterminism.lean::NEXP_subset_iUnion_NTIME  reproduces  Nondeterminism.lean::NP_subset_iUnion_NTIME: 62/114 = 54%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_clock_get: 205/377 = 54%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_emit: 275/506 = 54%
   Catalog.lean::f2_timed_control_init  reproduces  Nondeterminism.lean::cont_guess_initial: 113/208 = 54%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_skip_fixed: 383/705 = 54%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_ready_done: 393/724 = 54%
   Catalog.lean::a2_map_block  reproduces  Primitives.lean::extract_block: 355/654 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::f2_timed_branch_run  reproduces  Nondeterminism.lean::cont_core_run: 153/282 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Catalog.lean::f2_loopBorrow_run  reproduces  Loop.lean::loopHost_borrow_run: 288/531 = 54%
   MathlibBridge.lean::codePrimSkipTable2  reproduces  MathlibBridge.lean::codePrimSkipTable1: 135/249 = 54%
   Primitives.lean::splitEmit_suffix  reproduces  Loop.lean::loopReplay_run: 187/345 = 54%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Loop.lean::loopReplay_run: 187/345 = 54%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 469/866 = 54%
   Primitives.lean::pairValid_computes  reproduces  Primitives.lean::anyTrue_computes: 137/253 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_extract_run  reproduces  Primitives.lean::pairValid_run: 637/1177 = 54%
   Primitives.lean::splitBody_prepare  reproduces  Primitives.lean::splitBody_restore: 270/499 = 54%
   Loop.lean::loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 285/527 = 54%
   Primitives.lean::catalogPoly_unary_computes  reproduces  Primitives.lean::splitPoly_loop_end: 380/703 = 54%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 468/866 = 54%
   Nondeterminism.lean::a2Value_bits  reproduces  CodeParser.lean::codeBitsNat_bits: 87/161 = 54%
   Loop.lean::loopValue_bits  reproduces  CodeParser.lean::codeBitsNat_bits: 87/161 = 54%
   Catalog.lean::f2_loopValue_bits  reproduces  CodeParser.lean::codeBitsNat_bits: 87/161 = 54%
   Catalog.lean::f2_counterInc_bits  reproduces  CodeParser.lean::codeBitsNat_bits: 87/161 = 54%
   Nondeterminism.lean::cont_mask_count  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 81/150 = 54%
   Primitives.lean::splitEmit_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Primitives.lean::scanCopy_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Primitives.lean::extract_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Primitives.lean::emitterToken_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Primitives.lean::catalogPoly_loop  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Nondeterminism.lean::a3n_eq_double  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Nondeterminism.lean::a2Borrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   MathlibBridge.lean::bridge_statement  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::loopHost_borrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::emCall_finish_transfer  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::emCall_finish_rewind  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::emCall_finish_erase  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::emCall_finish_arg  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_loopBorrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_extract_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_counter_carry  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_catalogPoly_loop  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_backB  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_backA  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopFindTM: 491/910 = 54%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 467/866 = 54%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 467/866 = 54%
   Primitives.lean::extract_replay_finish  reproduces  UniversalStartup.lean::universalCapture_transfer: 69/128 = 54%
   Loop.lean::emCallPairEmbedding  reproduces  Loop.lean::emCallTripleEmbedding: 69/128 = 54%
   Catalog.lean::f2_extract_replay_finish  reproduces  UniversalStartup.lean::universalCapture_transfer: 69/128 = 54%
   Loop.lean::emCall_track_run  reproduces  Loop.lean::emCall_track_extent: 145/269 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   UniversalBlock.lean::universal_read_fixed  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 358/665 = 54%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 466/866 = 54%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 466/866 = 54%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 652/1212 = 54%
   Primitives.lean::lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 172/320 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::splitEmit_separator: 411/765 = 54%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_extra: 242/451 = 54%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 633/1181 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timed_replay  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_guess_return: 316/590 = 54%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedCut_skip_unary: 671/1254 = 54%
   Nondeterminism.lean::e3_find_eq  reproduces  Primitives.lean::splitFind_eq: 122/228 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Loop.lean::emCall_right_run: 92/172 = 53%
   Nondeterminism.lean::b2_unary_run  reproduces  Loop.lean::emCall_right_run: 92/172 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Primitives.lean::pairDup_computes  reproduces  Primitives.lean::emitterToken_separator: 116/217 = 53%
   Catalog.lean::f2_pairDup_computes  reproduces  Primitives.lean::emitterToken_separator: 116/217 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Universal.lean::timedCut_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 518/970 = 53%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_initial: 370/693 = 53%
   Nondeterminism.lean::e3_split_of_body  reproduces  Catalog.lean::f2_splitSolve_of_body: 717/1343 = 53%
   Seam.lean::seamRelease_run_pos  reproduces  Nondeterminism.lean::b2_unary_run: 72/135 = 53%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_prepare_final: 377/707 = 53%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_emitLoopTM: 1204/2258 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitter_compare_rewind: 479/899 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitter_compare_rewind: 479/899 = 53%
   Primitives.lean::splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Universal.lean::timedCapture_transfer: 66/124 = 53%
   Nondeterminism.lean::a2_load_rewind  reproduces  Universal.lean::timedCapture_transfer: 66/124 = 53%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Universal.lean::timedCapture_transfer: 66/124 = 53%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Universal.lean::timedCapture_transfer: 66/124 = 53%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_guess_return: 314/590 = 53%
   Nondeterminism.lean::e3_loop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 91/171 = 53%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::splitPrepare_scan: 340/639 = 53%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalBlock.lean::universal_skip_unary: 636/1196 = 53%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_table_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_skip_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalBlock.lean::universal_skip_unary  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalBlock.lean::universal_read_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_output_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_clock_success  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_clock_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_table_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_skip_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_read_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::splitRestore_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::splitPrepare_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::rawStrip_trim  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::rawStrip_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::mapBuffer_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::extract_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitter_compare_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitterToken_separator  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitterToken_double  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitterP2_erase_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::catalogPoly_setup  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::catalogPoly_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::catalogPoly_emit  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::anyTrue_run  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Loop.lean::loopHost_reject  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Loop.lean::emCall_right_scan  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_rawStrip_trim  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_reject  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_counter_increment  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Loop.lean::emCall_clear_left  reproduces  Primitives.lean::emitterP2_erase_scan: 168/316 = 53%
   Primitives.lean::rawStrip_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Primitives.lean::rawStrip_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Primitives.lean::extract_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Primitives.lean::extract_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_rawStrip_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Oracle.lean::runFrom_ofMultiTapeTM  reproduces  Oracle.lean::runFrom_plainEmptyOracle: 115/217 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_other: 152/287 = 53%
   Primitives.lean::splitPrepare_extra  reproduces  Primitives.lean::splitPrepare_scan: 338/639 = 53%
   Nondeterminism.lean::a2Borrow_step  reproduces  Loop.lean::loopReplay_step: 174/329 = 53%
   Catalog.lean::f2_loopBorrow_step  reproduces  Loop.lean::loopReplay_step: 174/329 = 53%
   Universal.lean::timedCut_prepare_next  reproduces  UniversalInterpreter.lean::universal_initial_skip: 513/970 = 53%
   Loop.lean::emCall_track_stamp  reproduces  Universal.lean::timedCapture_init: 168/318 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Primitives.lean::catalogFirstEntry: 198/375 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Primitives.lean::mapCfg  reproduces  Catalog.lean::f2_lenCfg: 95/180 = 53%
   Primitives.lean::mapValidate  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Primitives.lean::lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Primitives.lean::anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   OracleSim.lean::oracleShadowAction  reproduces  OracleSim.lean::oracleChoiceAction: 60/114 = 53%
   Universal.lean::timed_clock_success  reproduces  Universal.lean::timed_clock_timeout: 513/975 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   UniversalInterpreter.lean::universal_state_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Universal.lean::timedCut_state_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   CodeFormat.lean::actionBitsK  reproduces  CodeFormat.lean::actionBits₂: 93/177 = 53%
   Primitives.lean::pairDup_computes  reproduces  Primitives.lean::scanStep_right: 83/158 = 53%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanCopy_finish: 135/257 = 53%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeFormat.lean::codeReadWork_sound: 127/242 = 52%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Primitives.lean::mapValidate  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Loop.lean::loopReplay_run  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Catalog.lean::f2_loopReplay_run  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Catalog.lean::f2_counter_rewind  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_transfer: 764/1459 = 52%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_triple_pair: 122/233 = 52%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::extract_replay_finish: 156/298 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::extract_replay_finish: 156/298 = 52%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_skip_fixed: 369/705 = 52%
   Nondeterminism.lean::e3_find_eq  reproduces  Primitives.lean::emitterSplit_find: 123/235 = 52%
   CodeParser.lean::codeEraseVec  reproduces  CodeFormat.lean::codeEraseWork: 113/216 = 52%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::rawStrip_rewind: 368/704 = 52%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::rawStrip_rewind: 368/704 = 52%
   OracleSim.lean::oracleBack_run  reproduces  OracleSim.lean::oracleMarker_step: 199/381 = 52%
   OracleNondeterministic.lean::AcceptsWithin  reproduces  Nondeterminism.lean::choiceVerifier: 71/136 = 52%
   Catalog.lean::a2_map_setup  reproduces  Loop.lean::loopFuel_init: 214/410 = 52%
   Primitives.lean::catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 275/527 = 52%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_payload_scan: 359/688 = 52%
   Primitives.lean::emitter_bits_injective  reproduces  CodeParser.lean::codeBitsNat_bits: 84/161 = 52%
   Nondeterminism.lean::e3c_bits_injective  reproduces  CodeParser.lean::codeBitsNat_bits: 84/161 = 52%
   OracleSim.lean::oracleHost_initial  reproduces  OracleSim.lean::oraclePrepare_tail: 72/138 = 52%
   Universal.lean::timed_input_layout  reproduces  Universal.lean::timedClockPrefix_length: 73/140 = 52%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Primitives.lean::catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Primitives.lean::catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Oracle.lean::runFrom_plainEmptyOracle  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   CodeFormat.lean::codeReadActionK_sound  reproduces  CodeFormat.lean::codeReadWork_sound: 126/242 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Loop.lean::loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Primitives.lean::extract_replay_finish: 155/298 = 52%
   Nondeterminism.lean::a2_load_rewind  reproduces  Primitives.lean::extract_replay_finish: 155/298 = 52%
   Primitives.lean::catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Loop.lean::loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_counter_carry  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Primitives.lean::splitRestore_scan: 432/831 = 52%
   Primitives.lean::pairValid_run  reproduces  Primitives.lean::anyTrue_run: 413/795 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Primitives.lean::rawStrip_copy  reproduces  Primitives.lean::emitterP2_erase_scan: 164/316 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Primitives.lean::emitterP2_erase_scan: 164/316 = 52%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::a2Borrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Loop.lean::loopHost_borrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Catalog.lean::f2_loopBorrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Primitives.lean::emitterP2_erase_back  reproduces  Catalog.lean::f2_rawStrip_erase: 188/363 = 52%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_prepare_final: 366/707 = 52%
   Primitives.lean::extract_run  reproduces  Catalog.lean::f2_pairValid_run: 637/1231 = 52%
   Nondeterminism.lean::b2_verify_step  reproduces  Nondeterminism.lean::b2_ready_step: 327/632 = 52%
   UniversalInterpreter.lean::universalRecords  reproduces  Codes2Tape.lean::Code2TM.serialize: 160/310 = 52%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairFst: 80/155 = 52%
   Primitives.lean::splitEmit_separator  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Primitives.lean::lenSuffix_run  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Nondeterminism.lean::b2_verify_run  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Nondeterminism.lean::b2_guess_run  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Loop.lean::loopHost_fuel_copy  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_splitEmit_separator  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_lenSuffix_run  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 343/665 = 52%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Nondeterminism.lean::a2_load_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_reject_run: 282/547 = 52%
   OracleSim.lean::oracleLocalCfg  reproduces  OracleSim.lean::oracleBackCfg: 83/161 = 52%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Loop.lean::loopHost_fuel_return: 606/1176 = 52%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Loop.lean::loopHost_fuel_return: 606/1176 = 52%
   Nondeterminism.lean::e3_find_eq  reproduces  Catalog.lean::f2_splitFind_eq: 122/237 = 51%
   OracleNondeterministic.lean::AcceptsWithin  reproduces  Nondeterminism.lean::e3ChoiceVerifier: 71/138 = 51%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::scanCopy_suffix: 437/850 = 51%
   Nondeterminism.lean::b2_copy_step  reproduces  Nondeterminism.lean::b2_rewind_step: 201/391 = 51%
   Loop.lean::loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Primitives.lean::lenParse_run  reproduces  Primitives.lean::pairValid_run: 605/1177 = 51%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Nondeterminism.lean::a2Borrow_correct: 166/323 = 51%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 388/755 = 51%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedCut_initial_skip: 518/1008 = 51%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 322/627 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Primitives.lean::splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 242/472 = 51%
   Primitives.lean::mapPayload_replay  reproduces  Primitives.lean::rawStrip_replay: 208/406 = 51%
   Nondeterminism.lean::a2Borrow_run  reproduces  Loop.lean::loopHost_borrow_run: 272/531 = 51%
   Primitives.lean::splitEmit_separator  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   Catalog.lean::f2_splitEmit_separator  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   UniversalInterpreter.lean::universal_table_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Universal.lean::timed_output_back  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Universal.lean::timed_clock_back  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Universal.lean::timedCut_table_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::splitEmit_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::scanCopy_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::extract_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::catalogPoly_loop  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a3n_eq_double  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Loop.lean::emCall_finish_transfer  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Loop.lean::emCall_finish_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Loop.lean::emCall_finish_erase  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Loop.lean::emCall_finish_arg  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_extract_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_counter_increment  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_catalogPoly_loop  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::a2_map_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::a2_map_backB  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::a2_map_backA  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Universal.lean::timedCut_unary_copy  reproduces  UniversalBlock.lean::universal_skip_unary: 611/1196 = 51%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitter_compare_scan: 334/654 = 51%
   Primitives.lean::emitterP2_update_right  reproduces  Primitives.lean::emitterP2_words_clean: 72/141 = 51%
   Primitives.lean::emitterP2_update_left  reproduces  Primitives.lean::emitterP2_words_clean: 72/141 = 51%
   Catalog.lean::f2_lenParse_run  reproduces  Primitives.lean::pairValid_run: 601/1177 = 51%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 340/666 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Nondeterminism.lean::a2Borrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 174/341 = 51%
   Universal.lean::timedClockPrefix_length  reproduces  UniversalStartup.lean::universal_pair_length: 77/151 = 51%
   UniversalBlock.lean::universal_prepare_next  reproduces  Universal.lean::timedCut_initial_skip: 513/1008 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   CodeParser.lean::codeEraseVec  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeFormat.lean::codeEraseWork  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeFormat.lean::codeEraseActionK  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 156/307 = 51%
   Loop.lean::loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   CfgRecord.lean::recordStep_read_fields  reproduces  CfgRecord.lean::recordStep_write_back: 1389/2734 = 51%
   CodeParser.lean::codeReadUnary_sound  reproduces  CodeParser.lean::codeReadState_sound: 223/439 = 51%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Catalog.lean::f2_rawStrip_rewind: 368/725 = 51%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Catalog.lean::f2_rawStrip_rewind: 368/725 = 51%
   OracleSim.lean::oracleHost_initial  reproduces  OracleSim.lean::oraclePrepare_zero: 71/140 = 51%
   MathlibBridge.lean::bridge_scan  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Primitives.lean::catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_emit: 180/355 = 51%
   Catalog.lean::f2_catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_emit: 180/355 = 51%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 400/790 = 51%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitPrepare_extra: 228/451 = 51%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 322/637 = 51%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 322/637 = 51%
   Catalog.lean::f2_splitBody_rewind  reproduces  Primitives.lean::splitBody_restore: 252/499 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::rawStrip_replay: 205/406 = 50%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::rawStrip_replay: 205/406 = 50%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 155/307 = 50%
   Nondeterminism.lean::a2_load_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 155/307 = 50%
   Primitives.lean::mapPayload_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 208/412 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::emitterToken_double: 396/785 = 50%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalStartup.lean::universalPrefix_start  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalStartup.lean::universalPrefix_bits  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalInterpreter.lean::universal_skip_fixed  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalInterpreter.lean::universal_count_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalBlock.lean::universal_skip_unary  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalBlock.lean::universal_skip_groups  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalBlock.lean::universal_read_fixed  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalBlock.lean::universal_prepare_next  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedPrefix_complete  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedPrefix_code  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedPrefix_clock_end  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedPrefix_clock  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_unary_copy  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_skip_unary  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_skip_groups  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_skip_fixed  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_read_fixed  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_prepare_next  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_initial_skip  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_count_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::splitRestore_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::splitPrepare_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::splitEmbed_cut  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::rawStrip_trim  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::rawStrip_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::mapBuffer_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::extract_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitter_compare_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_prepare_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_erase_back  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::catalogPoly_setup  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::catalogPoly_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::catalogPoly_emit  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::anyTrue_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   MathlibBridge.lean::bridge_seed  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   MathlibBridge.lean::bridge_emit  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   MathlibBridge.lean::bridge_back  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Loop.lean::emCall_track_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Loop.lean::emCall_right_scan  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_rawStrip_trim  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_extract_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_counter_carry  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_anyTrue_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::a2_mapVirtual_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_skip_fixed: 355/705 = 50%
   Loop.lean::emCall_clear_run  reproduces  Loop.lean::emCall_clear_origin: 428/850 = 50%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_start_core: 432/858 = 50%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_start_core: 432/858 = 50%
   Loop.lean::emCall_track_computes  reproduces  Loop.lean::emCall_right_computes: 77/153 = 50%
   Loop.lean::emCall_right_computes  reproduces  Loop.lean::emCall_track_computes: 77/153 = 50%
   Loop.lean::emCall_track_stamp  reproduces  UniversalStartup.lean::universalCapture_init: 168/334 = 50%
   Catalog.lean::a2_mapVirtual  reproduces  VirtualInput.lean::vhostCfg: 91/181 = 50%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_inverse: 92/183 = 50%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedPrefix_live: 96/191 = 50%
   Universal.lean::timedCapture_start  reproduces  Universal.lean::timedPrefix_live: 96/191 = 50%
   Catalog.lean::compareTM_run_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::rawStrip_replay: 204/406 = 50%
   UniversalBlock.lean::universalActions  reproduces  UniversalInterpreter.lean::universalRecords: 105/209 = 50%
   Universal.lean::timedCut_Actions  reproduces  UniversalInterpreter.lean::universalRecords: 105/209 = 50%
   Loop.lean::loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   Primitives.lean::emitterAppend_run  reproduces  Catalog.lean::f2_scanCopy_finish: 135/269 = 50%
   Primitives.lean::splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 432/861 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_map_suffix  reproduces  Primitives.lean::scanCopy_suffix: 426/850 = 50%
   Loop.lean::loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 666/1329 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Nondeterminism.lean::a2Borrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 272/544 = 50%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   Primitives.lean::extract_replay_finish  reproduces  Primitives.lean::rawStrip_replay: 203/406 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Primitives.lean::rawStrip_replay: 203/406 = 50%
   Oracle.lean::runFrom_ofMultiTapeTM  reproduces  Catalog.lean::catalog_redirect_loop: 70/140 = 50%
   Nondeterminism.lean::e3_loop_result  reproduces  Nondeterminism.lean::e3_split_length: 70/140 = 50%
   Universal.lean::timedClockCfg  reproduces  Universal.lean::timed_laneCfg: 60/120 = 50%
```

### Full after output

```text
declarations screened: 1994; copy pairs (target reproduces >= half of source): 2218; reproduced text: 741,065 chars
   Catalog.lean::f2_loopBody_step  reproduces  Loop.lean::loopBody_step: 1094/1094 = 100%
   Primitives.lean::splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_cut: 985/985 = 100%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Primitives.lean::splitEmbed_cut: 985/985 = 100%
   Catalog.lean::f2_pairCountTM  reproduces  Primitives.lean::pairCountTM: 860/860 = 100%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Primitives.lean::scanCopy_suffix: 850/850 = 100%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_pairExtractTM: 793/793 = 100%
   Catalog.lean::f2_pairExtractTM  reproduces  Primitives.lean::pairExtractTM: 793/793 = 100%
   Catalog.lean::f2_catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_copy: 731/731 = 100%
   Loop.lean::loop_find_run  reproduces  Catalog.lean::f2_loop_find_run: 678/678 = 100%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_find_run: 678/678 = 100%
   Loop.lean::loop_halted_run  reproduces  Catalog.lean::a2_loop_halted_run: 659/659 = 100%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_halted_run: 659/659 = 100%
   Catalog.lean::f2_splitPrepare_run  reproduces  Primitives.lean::splitPrepare_run: 632/632 = 100%
   Catalog.lean::f2_scanTrues_run  reproduces  Primitives.lean::scanTrues_run: 608/608 = 100%
   Primitives.lean::splitRestoreTM  reproduces  Catalog.lean::f2_splitRestoreTM: 562/562 = 100%
   Catalog.lean::f2_splitRestoreTM  reproduces  Primitives.lean::splitRestoreTM: 562/562 = 100%
   Catalog.lean::f2_splitBodyStateDecidableEq  reproduces  Primitives.lean::splitBodyStateDecidableEq: 537/537 = 100%
   Loop.lean::loop_rewind_bounded  reproduces  Catalog.lean::f2_loop_rewind_bounded: 514/514 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Loop.lean::loop_rewind_bounded: 514/514 = 100%
   Catalog.lean::f2_catalogPolyCost_le  reproduces  Primitives.lean::catalogPolyCost_le: 485/485 = 100%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::scanCopy_run: 482/482 = 100%
   Primitives.lean::incFixedTM  reproduces  Catalog.lean::f2_incFixedTM: 474/474 = 100%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::incFixedTM: 474/474 = 100%
   Primitives.lean::splitBody_envelope  reproduces  Catalog.lean::f2_splitBody_envelope: 466/466 = 100%
   Catalog.lean::f2_splitBody_envelope  reproduces  Primitives.lean::splitBody_envelope: 466/466 = 100%
   Primitives.lean::rawStripTM  reproduces  Catalog.lean::f2_rawStripTM: 461/461 = 100%
   Catalog.lean::f2_rawStripTM  reproduces  Primitives.lean::rawStripTM: 461/461 = 100%
   Catalog.lean::f2_loopBody_run  reproduces  Loop.lean::loopBody_run: 452/452 = 100%
   Catalog.lean::f2_splitEmit_run  reproduces  Primitives.lean::splitEmit_run: 440/440 = 100%
   Primitives.lean::catalogRewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Primitives.lean::catalogRewind: 435/435 = 100%
   Loop.lean::loopBodyTM  reproduces  Catalog.lean::f2_loopBodyTM: 428/428 = 100%
   Catalog.lean::f2_loopBodyTM  reproduces  Loop.lean::loopBodyTM: 428/428 = 100%
   EXPCOM.lean::UniformMachineCode  reproduces  Codes2Tape.lean::UniformMachineCode2: 419/419 = 100%
   Codes2Tape.lean::UniformMachineCode2  reproduces  EXPCOM.lean::UniformMachineCode: 419/419 = 100%
   Catalog.lean::f2_loopFuel_init  reproduces  Loop.lean::loopFuel_init: 410/410 = 100%
   Nondeterminism.lean::a2Buffer_write  reproduces  Loop.lean::loopBuffer_write: 408/408 = 100%
   Nondeterminism.lean::a2Buffer_write  reproduces  Catalog.lean::f2_loopBuffer_write: 408/408 = 100%
   Loop.lean::loopBuffer_write  reproduces  Nondeterminism.lean::a2Buffer_write: 408/408 = 100%
   Loop.lean::loopBuffer_write  reproduces  Catalog.lean::f2_loopBuffer_write: 408/408 = 100%
   Catalog.lean::f2_loopBuffer_write  reproduces  Nondeterminism.lean::a2Buffer_write: 408/408 = 100%
   Catalog.lean::f2_loopBuffer_write  reproduces  Loop.lean::loopBuffer_write: 408/408 = 100%
   Primitives.lean::emitter_first_entry  reproduces  Loop.lean::emCall_first_entry: 403/403 = 100%
   Loop.lean::emCall_first_entry  reproduces  Primitives.lean::emitter_first_entry: 403/403 = 100%
   Primitives.lean::splitPrepareTM  reproduces  Catalog.lean::f2_splitPrepareTM: 399/399 = 100%
   Catalog.lean::f2_splitPrepareTM  reproduces  Primitives.lean::splitPrepareTM: 399/399 = 100%
   Primitives.lean::catalogMarker_cases  reproduces  Catalog.lean::f2_catalogMarker_cases: 396/396 = 100%
   Catalog.lean::f2_catalogMarker_cases  reproduces  Primitives.lean::catalogMarker_cases: 396/396 = 100%
   Primitives.lean::pairDupTM  reproduces  Catalog.lean::f2_pairDupTM: 386/386 = 100%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::pairDupTM: 386/386 = 100%
   Catalog.lean::f2_pairCount_computes  reproduces  Primitives.lean::pairCount_computes: 383/383 = 100%
   Primitives.lean::catalogFirstEntry  reproduces  Catalog.lean::f2_catalogFirstEntry: 375/375 = 100%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Primitives.lean::catalogFirstEntry: 375/375 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::f2_splitPos_succ  reproduces  Primitives.lean::splitPos_succ: 353/353 = 100%
   Primitives.lean::incFixed_cases  reproduces  Catalog.lean::f2_incFixed_cases: 352/352 = 100%
   Catalog.lean::f2_incFixed_cases  reproduces  Primitives.lean::incFixed_cases: 352/352 = 100%
   Catalog.lean::f2_loopBody_stop  reproduces  Loop.lean::loopBody_stop: 346/346 = 100%
   Catalog.lean::f2_loopReplay_run  reproduces  Loop.lean::loopReplay_run: 345/345 = 100%
   Loop.lean::loop_first_halt  reproduces  Catalog.lean::f2_loop_first_halt: 341/341 = 100%
   Catalog.lean::f2_loop_first_halt  reproduces  Loop.lean::loop_first_halt: 341/341 = 100%
   Primitives.lean::splitEmitTM  reproduces  Catalog.lean::f2_splitEmitTM: 327/327 = 100%
   Catalog.lean::f2_splitEmitTM  reproduces  Primitives.lean::splitEmitTM: 327/327 = 100%
   Primitives.lean::emitter_take_succ_eq  reproduces  Nondeterminism.lean::e3c_take_succ_eq: 291/291 = 100%
   Nondeterminism.lean::e3c_take_succ_eq  reproduces  Primitives.lean::emitter_take_succ_eq: 291/291 = 100%
   Catalog.lean::f2_loopCopy_erase  reproduces  Loop.lean::loopCopy_erase: 285/285 = 100%
   Primitives.lean::splitLoop_bound  reproduces  Catalog.lean::f2_splitLoop_bound: 276/276 = 100%
   Catalog.lean::f2_splitLoop_bound  reproduces  Primitives.lean::splitLoop_bound: 276/276 = 100%
   Loop.lean::loopFrame  reproduces  Catalog.lean::f2_loopFrame: 270/270 = 100%
   Catalog.lean::f2_loopFrame  reproduces  Loop.lean::loopFrame: 270/270 = 100%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Admin_apply: 264/264 = 100%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 264/264 = 100%
   Loop.lean::loop_output_length_le  reproduces  Catalog.lean::f2_loop_output_length_le: 254/254 = 100%
   Catalog.lean::f2_loop_output_length_le  reproduces  Loop.lean::loop_output_length_le: 254/254 = 100%
   Primitives.lean::pairValidTM  reproduces  Catalog.lean::f2_pairValidTM: 249/249 = 100%
   Catalog.lean::f2_pairValidTM  reproduces  Primitives.lean::pairValidTM: 249/249 = 100%
   Catalog.lean::f2_loopFuel_run  reproduces  Loop.lean::loopFuel_run: 230/230 = 100%
   Primitives.lean::emitter_bits_injective  reproduces  Nondeterminism.lean::e3c_bits_injective: 227/227 = 100%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Primitives.lean::emitter_bits_injective: 227/227 = 100%
   UniversalInterpreter.lean::universalStateTape_append  reproduces  Universal.lean::timedCut_StateTape_append: 218/218 = 100%
   Universal.lean::timedCut_StateTape_append  reproduces  UniversalInterpreter.lean::universalStateTape_append: 218/218 = 100%
   Catalog.lean::f2_splitPos_read  reproduces  Primitives.lean::splitPos_read: 215/215 = 100%
   Loop.lean::loopBodyCfg  reproduces  Catalog.lean::f2_loopBodyCfg: 212/212 = 100%
   Catalog.lean::f2_loopBodyCfg  reproduces  Loop.lean::loopBodyCfg: 212/212 = 100%
   Primitives.lean::catalogPrefixTM  reproduces  Catalog.lean::f2_catalogPrefixTM: 209/209 = 100%
   Catalog.lean::f2_catalogPrefixTM  reproduces  Primitives.lean::catalogPrefixTM: 209/209 = 100%
   UniversalStartup.lean::universal_pair_separator  reproduces  Universal.lean::timed_pair_separator: 207/207 = 100%
   Universal.lean::timed_pair_separator  reproduces  UniversalStartup.lean::universal_pair_separator: 207/207 = 100%
   Catalog.lean::f2_splitStep_orbit  reproduces  Primitives.lean::splitStep_orbit: 201/201 = 100%
   Catalog.lean::f2_splitCountCfg  reproduces  Primitives.lean::splitCountCfg: 201/201 = 100%
   UniversalBlock.lean::universalActionBits_decode  reproduces  Universal.lean::timedCut_ActionBits_decode: 191/191 = 100%
   Universal.lean::timedCut_ActionBits_decode  reproduces  UniversalBlock.lean::universalActionBits_decode: 191/191 = 100%
   Primitives.lean::splitRewindTM  reproduces  Catalog.lean::f2_splitRewindTM: 185/185 = 100%
   Catalog.lean::f2_splitRewindTM  reproduces  Primitives.lean::splitRewindTM: 185/185 = 100%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Universal.lean::timedCaptureCfg: 184/184 = 100%
   Universal.lean::timedCaptureCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 184/184 = 100%
   Catalog.lean::f2_lenCfg  reproduces  Primitives.lean::lenCfg: 177/177 = 100%
   Primitives.lean::anyTrueTM  reproduces  Catalog.lean::f2_anyTrueTM: 175/175 = 100%
   Catalog.lean::f2_anyTrueTM  reproduces  Primitives.lean::anyTrueTM: 175/175 = 100%
   Catalog.lean::f2_scanCfg_read  reproduces  Primitives.lean::scanCfg_read: 172/172 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Primitives.lean::splitCountAction  reproduces  Catalog.lean::f2_splitCountAction: 166/166 = 100%
   Catalog.lean::f2_splitCountAction  reproduces  Primitives.lean::splitCountAction: 166/166 = 100%
   Catalog.lean::f2_catalogPolyTape_write  reproduces  Primitives.lean::catalogPolyTape_write: 165/165 = 100%
   UniversalBlock.lean::universal_header_bound  reproduces  Universal.lean::timed_header_bound: 153/153 = 100%
   Universal.lean::timed_header_bound  reproduces  UniversalBlock.lean::universal_header_bound: 153/153 = 100%
   Loop.lean::loopControlAction  reproduces  Catalog.lean::f2_loopControlAction: 150/150 = 100%
   Catalog.lean::f2_loopControlAction  reproduces  Loop.lean::loopControlAction: 150/150 = 100%
   Catalog.lean::f2_loopCall  reproduces  Loop.lean::loopCall: 141/141 = 100%
   UniversalBlock.lean::universalActions  reproduces  Universal.lean::timedCut_Actions: 140/140 = 100%
   Universal.lean::timedCut_Actions  reproduces  UniversalBlock.lean::universalActions: 140/140 = 100%
   Nondeterminism.lean::e3ChoiceVerifier  reproduces  Nondeterminism.lean::choiceVerifier: 136/136 = 100%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamRelease_step_right: 135/135 = 100%
   Catalog.lean::f2_loopValue_bits  reproduces  Loop.lean::loopValue_bits: 135/135 = 100%
   Primitives.lean::SplitBodyState  reproduces  Catalog.lean::f2_SplitBodyState: 134/134 = 100%
   Catalog.lean::f2_SplitBodyState  reproduces  Primitives.lean::SplitBodyState: 134/134 = 100%
   Loop.lean::loopReplayTM  reproduces  Catalog.lean::f2_loopReplayTM: 130/130 = 100%
   Catalog.lean::f2_loopReplayTM  reproduces  Loop.lean::loopReplayTM: 130/130 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Nondeterminism.lean::e3_split_spec  reproduces  Nondeterminism.lean::certificateSplit_spec: 125/125 = 100%
   Nondeterminism.lean::certificateSplit_spec  reproduces  Nondeterminism.lean::e3_split_spec: 125/125 = 100%
   Loop.lean::loopFuelSource  reproduces  Catalog.lean::f2_loopFuelSource: 122/122 = 100%
   Catalog.lean::f2_splitPrepareReady  reproduces  Primitives.lean::splitPrepareReady: 122/122 = 100%
   Catalog.lean::f2_loopFuelSource  reproduces  Loop.lean::loopFuelSource: 122/122 = 100%
   UniversalStartup.lean::universal_live_before  reproduces  Universal.lean::timedCut_live_before: 121/121 = 100%
   Universal.lean::timedCut_live_before  reproduces  UniversalStartup.lean::universal_live_before: 121/121 = 100%
   Catalog.lean::f2_loopBodySource  reproduces  Loop.lean::loopBodySource: 119/119 = 100%
   Primitives.lean::catalogBuffer_erase  reproduces  Catalog.lean::f2_catalogBuffer_erase: 118/118 = 100%
   Loop.lean::emCall_erase_last  reproduces  Primitives.lean::catalogBuffer_erase: 118/118 = 100%
   Loop.lean::emCall_erase_last  reproduces  Catalog.lean::f2_catalogBuffer_erase: 118/118 = 100%
   Catalog.lean::f2_catalogBuffer_erase  reproduces  Primitives.lean::catalogBuffer_erase: 118/118 = 100%
   UniversalInterpreter.lean::universalInterpreterInitial  reproduces  Universal.lean::timedCut_InterpreterInitial: 113/113 = 100%
   Universal.lean::timedCut_InterpreterInitial  reproduces  UniversalInterpreter.lean::universalInterpreterInitial: 113/113 = 100%
   Primitives.lean::splitSafe_add  reproduces  Catalog.lean::f2_splitSafe_add: 110/110 = 100%
   Catalog.lean::f2_splitSafe_add  reproduces  Primitives.lean::splitSafe_add: 110/110 = 100%
   Catalog.lean::f2_loopCopy_final  reproduces  Loop.lean::loopCopy_final: 110/110 = 100%
   Primitives.lean::splitSafe_one  reproduces  Catalog.lean::f2_splitSafe_one: 107/107 = 100%
   Catalog.lean::f2_splitSafe_one  reproduces  Primitives.lean::splitSafe_one: 107/107 = 100%
   Catalog.lean::f2_splitRestoreScan  reproduces  Primitives.lean::splitRestoreScan: 106/106 = 100%
   Primitives.lean::catalogFind_congr  reproduces  Nondeterminism.lean::e3_find_congr: 104/104 = 100%
   Primitives.lean::catalogFind_congr  reproduces  Catalog.lean::f2_catalogFind_congr: 104/104 = 100%
   Nondeterminism.lean::e3_find_congr  reproduces  Primitives.lean::catalogFind_congr: 104/104 = 100%
   Nondeterminism.lean::e3_find_congr  reproduces  Catalog.lean::f2_catalogFind_congr: 104/104 = 100%
   Catalog.lean::f2_catalogFind_congr  reproduces  Primitives.lean::catalogFind_congr: 104/104 = 100%
   Catalog.lean::f2_catalogFind_congr  reproduces  Nondeterminism.lean::e3_find_congr: 104/104 = 100%
   UniversalInterpreter.lean::universalInterpreterBase  reproduces  Universal.lean::timedCut_InterpreterBase: 102/102 = 100%
   Universal.lean::timedCut_InterpreterBase  reproduces  UniversalInterpreter.lean::universalInterpreterBase: 102/102 = 100%
   Loop.lean::loopBodyTM  reproduces  Oracle.lean::Action.extend: 101/101 = 100%
   Catalog.lean::f2_loopBodyTM  reproduces  Oracle.lean::Action.extend: 101/101 = 100%
   Catalog.lean::f2_splitPrepareScan  reproduces  Primitives.lean::splitPrepareScan: 97/97 = 100%
   Catalog.lean::f2_splitSafe_join  reproduces  Primitives.lean::splitSafe_join: 95/95 = 100%
   Loop.lean::loop_orbit_inv  reproduces  Catalog.lean::f2_loop_orbit_inv: 94/94 = 100%
   Catalog.lean::f2_loop_orbit_inv  reproduces  Loop.lean::loop_orbit_inv: 94/94 = 100%
   Catalog.lean::f2_loopBorrowPos_le  reproduces  Loop.lean::loopBorrowPos_le: 93/93 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   Catalog.lean::computesFunInTime_pairEncodeFixed_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairEncodeFixed: 91/91 = 100%
   Loop.lean::loopFuelCfg  reproduces  Catalog.lean::f2_loopFuelCfg: 90/90 = 100%
   Catalog.lean::f2_loopFuelCfg  reproduces  Loop.lean::loopFuelCfg: 90/90 = 100%
   Primitives.lean::CatalogPolyControl  reproduces  Catalog.lean::f2_CatalogPolyControl: 89/89 = 100%
   Nondeterminism.lean::a2Buffer_read  reproduces  Loop.lean::loopBuffer_read: 89/89 = 100%
   Nondeterminism.lean::a2Buffer_read  reproduces  Catalog.lean::f2_loopBuffer_read: 89/89 = 100%
   Loop.lean::loopBuffer_read  reproduces  Nondeterminism.lean::a2Buffer_read: 89/89 = 100%
   Loop.lean::loopBuffer_read  reproduces  Catalog.lean::f2_loopBuffer_read: 89/89 = 100%
   Catalog.lean::f2_loopBuffer_read  reproduces  Nondeterminism.lean::a2Buffer_read: 89/89 = 100%
   Catalog.lean::f2_loopBuffer_read  reproduces  Loop.lean::loopBuffer_read: 89/89 = 100%
   Catalog.lean::f2_CatalogPolyControl  reproduces  Primitives.lean::CatalogPolyControl: 89/89 = 100%
   UniversalInterpreter.lean::universalEval_reads  reproduces  Universal.lean::timedCut_Eval_reads: 88/88 = 100%
   Universal.lean::timedCut_Eval_reads  reproduces  UniversalInterpreter.lean::universalEval_reads: 88/88 = 100%
   Loop.lean::loop_fuel_width  reproduces  Catalog.lean::f2_loop_fuel_width: 87/87 = 100%
   Catalog.lean::f2_loop_fuel_width  reproduces  Loop.lean::loop_fuel_width: 87/87 = 100%
   Catalog.lean::f2_loopFrame_payload  reproduces  Loop.lean::loopFrame_payload: 79/79 = 100%
   Nondeterminism.lean::contSplitWord  reproduces  CertShell.lean::certSplitWord: 74/74 = 100%
   CertShell.lean::certSplitWord  reproduces  Nondeterminism.lean::contSplitWord: 74/74 = 100%
   UniversalBlock.lean::universalHeader  reproduces  Universal.lean::timedCut_Header: 73/73 = 100%
   Universal.lean::timedCut_Header  reproduces  UniversalBlock.lean::universalHeader: 73/73 = 100%
   UniversalBlock.lean::universalActions_lookup  reproduces  Universal.lean::timedCut_Actions_lookup: 68/68 = 100%
   Universal.lean::timedCut_Actions_lookup  reproduces  UniversalBlock.lean::universalActions_lookup: 68/68 = 100%
   UniversalInterpreter.lean::universal_table_read  reproduces  Universal.lean::timedCut_table_read: 61/61 = 100%
   Universal.lean::timedCut_table_read  reproduces  UniversalInterpreter.lean::universal_table_read: 61/61 = 100%
   Primitives.lean::splitRestoreClean  reproduces  Catalog.lean::f2_splitRestoreClean: 61/61 = 100%
   Catalog.lean::f2_splitRestoreClean  reproduces  Primitives.lean::splitRestoreClean: 61/61 = 100%
   Catalog.lean::f2_loopFlag_clear  reproduces  Loop.lean::loopFlag_clear: 60/60 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::transferTM  reproduces  Catalog.lean::copyTM: 475/476 = 100%
   Primitives.lean::emitterSplit_find  reproduces  Primitives.lean::splitFind_eq: 227/228 = 100%
   UniversalBlock.lean::universal_apply_record  reproduces  Universal.lean::timed_apply_record: 1357/1366 = 99%
   Universal.lean::timed_apply_record  reproduces  UniversalBlock.lean::universal_apply_record: 1357/1366 = 99%
   Loop.lean::loopBody_run  reproduces  Catalog.lean::f2_loopBody_run: 452/455 = 99%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   UniversalInterpreter.lean::universalStartupBound  reproduces  Universal.lean::timedStartupBound: 130/131 = 99%
   Universal.lean::timedStartupBound  reproduces  UniversalInterpreter.lean::universalStartupBound: 130/131 = 99%
   MathlibBridge.lean::codePrimBitsNat  reproduces  MathlibBridge.lean::bridgePrimNumber: 128/129 = 99%
   MathlibBridge.lean::bridgePrimNumber  reproduces  MathlibBridge.lean::codePrimBitsNat: 128/129 = 99%
   Catalog.lean::f2_loopHost_contracts  reproduces  Loop.lean::loopHost_contracts: 3565/3596 = 99%
   Primitives.lean::emitterToken_double  reproduces  Primitives.lean::emitterToken_separator: 215/217 = 99%
   Universal.lean::timedCut_read_fixed  reproduces  UniversalBlock.lean::universal_read_fixed: 1863/1881 = 99%
   UniversalBlock.lean::universal_skip_records  reproduces  Universal.lean::timedCut_skip_records: 729/737 = 99%
   Universal.lean::timedCut_skip_records  reproduces  UniversalBlock.lean::universal_skip_records: 729/738 = 99%
   Catalog.lean::f2_catalogPolyUnaryTM  reproduces  Primitives.lean::catalogPolyUnaryTM: 788/798 = 99%
   Catalog.lean::f2_extract_run  reproduces  Primitives.lean::extract_run: 1830/1854 = 99%
   Loop.lean::loopBody_step  reproduces  Catalog.lean::f2_loopBody_step: 1094/1109 = 99%
   Universal.lean::timedCut_skip_groups  reproduces  UniversalBlock.lean::universal_skip_groups: 1873/1900 = 99%
   Nondeterminism.lean::choiceVerifier  reproduces  Nondeterminism.lean::e3ChoiceVerifier: 136/138 = 99%
   Primitives.lean::scanTrues_run  reproduces  Catalog.lean::f2_scanTrues_run: 608/617 = 99%
   Primitives.lean::splitStep_orbit  reproduces  Catalog.lean::f2_splitStep_orbit: 201/204 = 99%
   Primitives.lean::splitCountCfg  reproduces  Catalog.lean::f2_splitCountCfg: 201/204 = 99%
   Catalog.lean::f2_extract_suffix  reproduces  Primitives.lean::extract_suffix: 1125/1142 = 99%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::splitEmit_double: 1402/1424 = 98%
   Primitives.lean::lenCfg  reproduces  Catalog.lean::f2_lenCfg: 177/180 = 98%
   Catalog.lean::f2_catalogPoly_loop  reproduces  Primitives.lean::catalogPoly_loop: 3777/3842 = 98%
   Loop.lean::loopBody_stop  reproduces  Catalog.lean::f2_loopBody_stop: 346/352 = 98%
   Loop.lean::loopReplay_run  reproduces  Catalog.lean::f2_loopReplay_run: 345/351 = 98%
   Catalog.lean::f2_splitBodyTM  reproduces  Primitives.lean::splitBodyTM: 676/688 = 98%
   Primitives.lean::catalogPolyCost_le  reproduces  Catalog.lean::f2_catalogPolyCost_le: 485/494 = 98%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  Primitives.lean::catalogPoly_rewind: 1010/1030 = 98%
   Primitives.lean::splitEmit_run  reproduces  Catalog.lean::f2_splitEmit_run: 440/449 = 98%
   Catalog.lean::f2_loopHost  reproduces  Loop.lean::loopHostM: 2368/2417 = 98%
   Loop.lean::loopCopy_erase  reproduces  Catalog.lean::f2_loopCopy_erase: 285/291 = 98%
   Primitives.lean::scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 850/868 = 98%
   Loop.lean::loopCall  reproduces  Catalog.lean::f2_loopCall: 141/144 = 98%
   Catalog.lean::f2_splitLoop_result  reproduces  Primitives.lean::splitLoop_result: 226/231 = 98%
   Loop.lean::loopBorrowPos_le  reproduces  Nondeterminism.lean::a2BorrowPos_le: 89/91 = 98%
   Catalog.lean::f2_loopBorrowPos_le  reproduces  Nondeterminism.lean::a2BorrowPos_le: 89/91 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamRelease_step_right: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalBlock.lean::universal_apply_record  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   Universal.lean::timedCut_Interpreter_first  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Primitives.lean::pairCount_computes  reproduces  Catalog.lean::f2_pairCount_computes: 383/392 = 98%
   Primitives.lean::emitterP2SmallIndex  reproduces  Primitives.lean::emitterP2PairIndex: 207/212 = 98%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::extract_replay: 567/581 = 98%
   Loop.lean::loopBodySource  reproduces  Catalog.lean::f2_loopBodySource: 119/122 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Catalog.lean::f2_rawStrip_erase  reproduces  Primitives.lean::rawStrip_erase: 345/354 = 97%
   Loop.lean::loopFuel_run  reproduces  Catalog.lean::f2_loopFuel_run: 230/236 = 97%
   Catalog.lean::f2_splitCount_run  reproduces  Primitives.lean::splitCount_run: 898/922 = 97%
   Nondeterminism.lean::choiceVerifier_no_split  reproduces  Nondeterminism.lean::e3_choice_no_split: 145/149 = 97%
   Universal.lean::timedCut_skip_fixed  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 647/665 = 97%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::rawStrip_replay: 395/406 = 97%
   Primitives.lean::splitPos_read  reproduces  Catalog.lean::f2_splitPos_read: 215/221 = 97%
   Universal.lean::timedCut_table_rewind  reproduces  UniversalInterpreter.lean::universal_table_rewind: 637/655 = 97%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Primitives.lean::catalogPoly_unary_computes: 1223/1258 = 97%
   Primitives.lean::catalogPrefixTM_copy  reproduces  Catalog.lean::f2_catalogPrefixTM_copy: 731/752 = 97%
   Loop.lean::loopFuel_init  reproduces  Catalog.lean::f2_loopFuel_init: 410/422 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 403/415 = 97%
   Universal.lean::timedCut_select  reproduces  UniversalBlock.lean::universal_select: 2103/2166 = 97%
   UniversalBlock.lean::universal_skip_record  reproduces  Universal.lean::timedCut_skip_record: 797/821 = 97%
   Catalog.lean::f2_splitEmitCfg  reproduces  Primitives.lean::splitEmitCfg: 97/100 = 97%
   Universal.lean::timedCut_skip_unary  reproduces  UniversalBlock.lean::universal_skip_unary: 1160/1196 = 97%
   Primitives.lean::scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_run: 482/497 = 97%
   UniversalBlock.lean::universal_read_fixed  reproduces  Universal.lean::timedCut_read_fixed: 1863/1921 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Primitives.lean::splitSafe_join  reproduces  Catalog.lean::f2_splitSafe_join: 95/98 = 97%
   Catalog.lean::f2_splitFind_eq  reproduces  Primitives.lean::splitFind_eq: 221/228 = 97%
   Primitives.lean::catalogPolyUnaryTM  reproduces  Catalog.lean::f2_catalogPolyUnaryTM: 788/813 = 97%
   Catalog.lean::f2_scanCopy_finish  reproduces  Primitives.lean::scanCopy_finish: 249/257 = 97%
   Loop.lean::loopBorrowPos_le  reproduces  Catalog.lean::f2_loopBorrowPos_le: 93/96 = 97%
   Primitives.lean::scanTrues_run  reproduces  Primitives.lean::scanStep_right: 153/158 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Primitives.lean::emitterP2_right_frame  reproduces  Primitives.lean::emitterP2_left_frame: 273/282 = 97%
   Catalog.lean::f2_lenStart  reproduces  Primitives.lean::lenStart: 1606/1659 = 97%
   Catalog.lean::f2_extract_block  reproduces  Primitives.lean::extract_block: 633/654 = 97%
   Primitives.lean::splitBodyStateDecidableEq  reproduces  Catalog.lean::f2_splitBodyStateDecidableEq: 537/555 = 97%
   Universal.lean::timedCut_skip_record  reproduces  UniversalBlock.lean::universal_skip_record: 797/824 = 97%
   Primitives.lean::pairCountTM  reproduces  Catalog.lean::f2_pairCountTM: 860/890 = 97%
   Primitives.lean::scanCfg_read  reproduces  Catalog.lean::f2_scanCfg_read: 172/178 = 97%
   UniversalBlock.lean::universal_skip_groups  reproduces  Universal.lean::timedCut_skip_groups: 1873/1939 = 97%
   Primitives.lean::splitFind_eq  reproduces  Primitives.lean::emitterSplit_find: 227/235 = 97%
   Primitives.lean::extract_replay  reproduces  Catalog.lean::f2_extract_replay: 567/587 = 97%
   Catalog.lean::f2_loopHost_replay  reproduces  Loop.lean::loopHost_replay: 1032/1069 = 97%
   Primitives.lean::catalogPolyTape_write  reproduces  Catalog.lean::f2_catalogPolyTape_write: 165/171 = 96%
   Primitives.lean::emitterP2_left_frame  reproduces  Primitives.lean::emitterP2_right_frame: 273/283 = 96%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Primitives.lean::splitEmit_suffix: 1056/1095 = 96%
   Catalog.lean::f2_splitCount_over  reproduces  Primitives.lean::splitCount_over: 132/137 = 96%
   Loop.lean::loopFrame_payload  reproduces  Catalog.lean::f2_loopFrame_payload: 79/82 = 96%
   Universal.lean::timedCut_initial_skip  reproduces  UniversalInterpreter.lean::universal_initial_skip: 934/970 = 96%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::extract_rewind: 718/746 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Loop.lean::loopHost_frame_replay: 888/923 = 96%
   Catalog.lean::f2_splitRestore_scan  reproduces  Primitives.lean::splitRestore_scan: 799/831 = 96%
   Catalog.lean::f2_extract_first  reproduces  Primitives.lean::extract_first: 274/285 = 96%
   Catalog.lean::f2_extract_finish  reproduces  Primitives.lean::extract_finish: 595/619 = 96%
   Catalog.lean::f2_rawStrip_finish  reproduces  Primitives.lean::rawStrip_finish: 270/281 = 96%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::computesFunInTime_pairConcat: 147/153 = 96%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::rawStrip_replay: 390/406 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::rawStrip_replay: 390/406 = 96%
   Catalog.lean::f2_loopReplay_step  reproduces  Loop.lean::loopReplay_step: 316/329 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Universal.lean::timedCut_prepare_next  reproduces  UniversalBlock.lean::universal_prepare_next: 1959/2040 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   UniversalStartup.lean::universalCapture_transfer  reproduces  Universal.lean::timedCapture_transfer: 119/124 = 96%
   Primitives.lean::splitPos_succ  reproduces  Catalog.lean::f2_splitPos_succ: 353/368 = 96%
   Primitives.lean::extract_run  reproduces  Catalog.lean::f2_extract_run: 1830/1908 = 96%
   Primitives.lean::rawStrip_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 395/412 = 96%
   Catalog.lean::f2_catalogPrefixTM_computes  reproduces  Primitives.lean::catalogPrefixTM_computes: 369/385 = 96%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::pairDup_double: 1127/1176 = 96%
   Primitives.lean::splitBodyTM  reproduces  Catalog.lean::f2_splitBodyTM: 676/706 = 96%
   Loop.lean::loopValue_bits  reproduces  Catalog.lean::f2_loopValue_bits: 135/141 = 96%
   Nondeterminism.lean::a2BorrowPos_le  reproduces  Loop.lean::loopBorrowPos_le: 89/93 = 96%
   Nondeterminism.lean::certificateSplit_none_iff  reproduces  Nondeterminism.lean::e3_split_none_iff: 155/162 = 96%
   Primitives.lean::emitterP2_body_erase_right  reproduces  Primitives.lean::emitterP2_body_erase_left: 1078/1127 = 96%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedCut_unary_copy: 942/985 = 96%
   UniversalBlock.lean::universal_select  reproduces  Universal.lean::timedCut_select: 2103/2199 = 96%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_double: 1402/1466 = 96%
   Catalog.lean::f2_lenParse_block  reproduces  Primitives.lean::lenParse_block: 700/732 = 96%
   UniversalInterpreter.lean::universal_state_rewind  reproduces  Universal.lean::timedCut_state_rewind: 393/411 = 96%
   Universal.lean::timedCut_state_rewind  reproduces  UniversalInterpreter.lean::universal_state_rewind: 393/411 = 96%
   Catalog.lean::f2_loopControl_payload  reproduces  Loop.lean::loopControl_payload: 235/246 = 96%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 827/866 = 95%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 827/866 = 95%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::splitRestore_rewind: 754/790 = 95%
   Universal.lean::timedCut_unary_copy  reproduces  UniversalInterpreter.lean::universal_unary_copy: 942/987 = 95%
   Catalog.lean::f2_splitEmit_separator  reproduces  Primitives.lean::splitEmit_separator: 730/765 = 95%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Primitives.lean::splitLoop_result  reproduces  Catalog.lean::f2_splitLoop_result: 226/237 = 95%
   Primitives.lean::computesFunInTime_stripLast  reproduces  Catalog.lean::f2_strip_linear: 1616/1695 = 95%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   Primitives.lean::splitPrepareReady  reproduces  Catalog.lean::f2_splitPrepareReady: 122/128 = 95%
   Catalog.lean::f2_extract_replay_finish  reproduces  Primitives.lean::extract_replay_finish: 284/298 = 95%
   Loop.lean::loopFlag_clear  reproduces  Catalog.lean::f2_loopFlag_clear: 60/63 = 95%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 719/755 = 95%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::f2_splitCount_run: 898/943 = 95%
   UniversalBlock.lean::universal_serialization_actions  reproduces  UniversalInterpreter.lean::universal_serialization_header: 589/619 = 95%
   Universal.lean::timedCut_serialization_actions  reproduces  UniversalInterpreter.lean::universal_serialization_header: 589/619 = 95%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_halted_run: 627/659 = 95%
   Loop.lean::loop_run  reproduces  Catalog.lean::a2_loop_halted_run: 627/659 = 95%
   Primitives.lean::emitterP2_body_erase_left  reproduces  Primitives.lean::emitterP2_body_erase_right: 1078/1134 = 95%
   Nondeterminism.lean::e3_choice_append  reproduces  Nondeterminism.lean::choiceVerifier_append: 192/202 = 95%
   Primitives.lean::rawStrip_erase  reproduces  Catalog.lean::f2_rawStrip_erase: 345/363 = 95%
   Catalog.lean::f2_loopHost_accept  reproduces  Loop.lean::loopHost_accept: 2127/2238 = 95%
   Catalog.lean::f2_loopDebit_value  reproduces  Loop.lean::loopDebit_value: 187/197 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Loop.lean::loopHostM  reproduces  Catalog.lean::f2_loopHost: 2368/2495 = 95%
   Catalog.lean::f2_rawStrip_trim  reproduces  Primitives.lean::rawStrip_trim: 575/606 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::computesFunInTime_pairFst: 147/155 = 95%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 551/581 = 95%
   Loop.lean::loopCopy_final  reproduces  Catalog.lean::f2_loopCopy_final: 110/116 = 95%
   UniversalBlock.lean::universal_serialization_actions  reproduces  Universal.lean::timedCut_serialization_actions: 767/809 = 95%
   Universal.lean::timedCut_serialization_actions  reproduces  UniversalBlock.lean::universal_serialization_actions: 767/809 = 95%
   Nondeterminism.lean::a2_compile  reproduces  Nondeterminism.lean::b2_compile: 924/975 = 95%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_scan: 605/639 = 95%
   Primitives.lean::extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 390/412 = 95%
   Primitives.lean::splitRestoreScan  reproduces  Catalog.lean::f2_splitRestoreScan: 106/112 = 95%
   Primitives.lean::splitPrepare_run  reproduces  Catalog.lean::f2_splitPrepare_run: 632/668 = 95%
   Catalog.lean::f2_catalogPoly_copy  reproduces  Primitives.lean::catalogPoly_copy: 665/703 = 95%
   Catalog.lean::f2_catalogPoly_start  reproduces  Primitives.lean::catalogPoly_start: 833/881 = 95%
   Primitives.lean::catalogPoly_loop  reproduces  Catalog.lean::f2_catalogPoly_loop: 3777/3995 = 95%
   Primitives.lean::extract_suffix  reproduces  Catalog.lean::f2_extract_suffix: 1125/1190 = 95%
   Primitives.lean::catalogPoly_unary_computes  reproduces  Catalog.lean::f2_catalogPoly_unary_computes: 1223/1294 = 95%
   Primitives.lean::catalogPoly_rewind  reproduces  Catalog.lean::f2_catalogPoly_rewind: 1010/1069 = 94%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_bank_initial: 3070/3250 = 94%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Interpreter_first: 272/288 = 94%
   Primitives.lean::lenStart  reproduces  Catalog.lean::f2_lenStart: 1606/1701 = 94%
   Loop.lean::loopControl_payload  reproduces  Catalog.lean::f2_loopControl_payload: 235/249 = 94%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Eval_reads: 83/88 = 94%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   Universal.lean::timedCut_Admin_apply  reproduces  Universal.lean::timedCut_Eval_reads: 83/88 = 94%
   Primitives.lean::splitCount_over  reproduces  Catalog.lean::f2_splitCount_over: 132/140 = 94%
   Catalog.lean::f2_splitSolve_of_body  reproduces  Primitives.lean::splitSolve_of_body: 886/940 = 94%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::rawStrip_rewind: 663/704 = 94%
   Primitives.lean::splitPrepareScan  reproduces  Catalog.lean::f2_splitPrepareScan: 97/103 = 94%
   Loop.lean::loopHost_round  reproduces  Catalog.lean::f2_loopHost_round: 1989/2114 = 94%
   Catalog.lean::f2_rawStrip_copy  reproduces  Primitives.lean::rawStrip_copy: 699/743 = 94%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Primitives.lean::splitPrepare_extra: 424/451 = 94%
   Catalog.lean::f2_loopDebit_success  reproduces  Loop.lean::loopDebit_success: 141/150 = 94%
   Catalog.lean::f2_splitRestore_first  reproduces  Primitives.lean::splitRestore_first: 608/647 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Universal.lean::timedCut_count_run  reproduces  UniversalInterpreter.lean::universal_count_run: 2197/2342 = 94%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 272/290 = 94%
   Primitives.lean::extract_block  reproduces  Catalog.lean::f2_extract_block: 633/675 = 94%
   Primitives.lean::incFixed_computes  reproduces  Primitives.lean::scanStep_right: 148/158 = 94%
   Catalog.lean::f2_splitFind_eq  reproduces  Primitives.lean::emitterSplit_find: 220/235 = 94%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_extract_rewind: 718/767 = 94%
   Catalog.lean::f2_exists_loopFind_space  reproduces  Loop.lean::exists_loopFindTM: 851/910 = 94%
   Catalog.lean::copyTM  reproduces  Catalog.lean::transferTM: 475/508 = 94%
   Catalog.lean::f2_splitSolve_source  reproduces  Primitives.lean::splitSolve_source: 397/425 = 93%
   Loop.lean::loopHost_replay  reproduces  Catalog.lean::f2_loopHost_replay: 1032/1105 = 93%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_setup: 533/571 = 93%
   Catalog.lean::f2_lenParse_run  reproduces  Primitives.lean::lenParse_run: 1533/1643 = 93%
   Primitives.lean::splitFind_eq  reproduces  Catalog.lean::f2_splitFind_eq: 221/237 = 93%
   Catalog.lean::f2_loopBodyPadded  reproduces  Loop.lean::loopBodyPadded: 137/147 = 93%
   Catalog.lean::f2_lenParse_first  reproduces  Primitives.lean::lenParse_first: 287/308 = 93%
   Loop.lean::loopHost_frame_replay  reproduces  Catalog.lean::f2_loopHost_frame_replay: 888/953 = 93%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_pair_get: 257/276 = 93%
   Catalog.lean::f2_splitCount_accept  reproduces  Primitives.lean::splitCount_accept: 266/286 = 93%
   Primitives.lean::pairDup_double  reproduces  Catalog.lean::f2_pairDup_double: 1127/1212 = 93%
   Universal.lean::timedCapture_transfer  reproduces  UniversalStartup.lean::universalCapture_transfer: 119/128 = 93%
   Primitives.lean::catalogPrefixTM_computes  reproduces  Catalog.lean::f2_catalogPrefixTM_computes: 369/397 = 93%
   Primitives.lean::splitEmit_suffix  reproduces  Catalog.lean::f2_splitEmit_suffix: 1056/1137 = 93%
   Universal.lean::timedSix  reproduces  Universal.lean::timedFive: 78/84 = 93%
   Primitives.lean::emitterSplit_find  reproduces  Catalog.lean::f2_splitFind_eq: 220/237 = 93%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_trace: 1160/1250 = 93%
   Primitives.lean::splitRestore_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 799/861 = 93%
   Nondeterminism.lean::choiceVerifier_append  reproduces  Nondeterminism.lean::e3_choice_append: 192/207 = 93%
   Nondeterminism.lean::a2BorrowPos_le  reproduces  Catalog.lean::f2_loopBorrowPos_le: 89/96 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Loop.lean::loopReplay_step  reproduces  Catalog.lean::f2_loopReplay_step: 316/341 = 93%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_initial_skip: 934/1008 = 93%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 719/776 = 93%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 754/814 = 93%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::emitterToken_separator: 201/217 = 93%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_small_frame: 539/582 = 93%
   Loop.lean::loopHost_accept  reproduces  Catalog.lean::f2_loopHost_accept: 2127/2297 = 93%
   Primitives.lean::lenParse_block  reproduces  Catalog.lean::f2_lenParse_block: 700/756 = 93%
   Catalog.lean::f2_rawStrip_computes  reproduces  Primitives.lean::rawStrip_computes: 650/702 = 93%
   Primitives.lean::rawStrip_trim  reproduces  Catalog.lean::f2_rawStrip_trim: 575/621 = 93%
   Primitives.lean::scanCopy_finish  reproduces  Catalog.lean::f2_scanCopy_finish: 249/269 = 93%
   Primitives.lean::extract_finish  reproduces  Catalog.lean::f2_extract_finish: 595/643 = 93%
   Primitives.lean::extract_replay_finish  reproduces  Catalog.lean::f2_extract_replay_finish: 284/307 = 93%
   UniversalBlock.lean::universal_skip_unary  reproduces  Universal.lean::timedCut_skip_unary: 1160/1254 = 93%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Primitives.lean::catalogPoly_emit: 468/506 = 92%
   Catalog.lean::f2_pairExtract_computes  reproduces  Primitives.lean::pairExtract_computes: 443/479 = 92%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_pair_frame: 539/583 = 92%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::scanStep_right: 146/158 = 92%
   Nondeterminism.lean::e3_choice_no_split  reproduces  Nondeterminism.lean::choiceVerifier_no_split: 145/157 = 92%
   UniversalBlock.lean::universal_lookup_parts  reproduces  Universal.lean::timedCut_lookup_parts: 1305/1415 = 92%
   Universal.lean::timedCut_lookup_parts  reproduces  UniversalBlock.lean::universal_lookup_parts: 1305/1416 = 92%
   Primitives.lean::rawStrip_finish  reproduces  Catalog.lean::f2_rawStrip_finish: 270/293 = 92%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Loop.lean::loopHost_borrow_run: 489/531 = 92%
   Catalog.lean::f2_pairValid_run  reproduces  Primitives.lean::pairValid_run: 1083/1177 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   UniversalInterpreter.lean::universal_skip_fixed  reproduces  Universal.lean::timedCut_skip_fixed: 647/705 = 92%
   Catalog.lean::f2_lenSuffix_run  reproduces  Primitives.lean::lenSuffix_run: 1436/1566 = 92%
   UniversalInterpreter.lean::universal_table_rewind  reproduces  Universal.lean::timedCut_table_rewind: 637/695 = 92%
   Primitives.lean::emitterP2PairIndex  reproduces  Primitives.lean::emitterP2SmallIndex: 207/226 = 92%
   Primitives.lean::splitEmitCfg  reproduces  Catalog.lean::f2_splitEmitCfg: 97/106 = 92%
   Primitives.lean::catalogPoly_copy  reproduces  Catalog.lean::f2_catalogPoly_copy: 665/727 = 91%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 663/725 = 91%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Nondeterminism.lean::b2_compile  reproduces  Nondeterminism.lean::a2_compile: 924/1011 = 91%
   Primitives.lean::extract_first  reproduces  Catalog.lean::f2_extract_first: 274/300 = 91%
   Loop.lean::loopBodyPadded  reproduces  Catalog.lean::f2_loopBodyPadded: 137/150 = 91%
   Catalog.lean::f2_anyTrue_computes  reproduces  Primitives.lean::anyTrue_computes: 231/253 = 91%
   Catalog.lean::f2_incFixed_computes  reproduces  Primitives.lean::incFixed_computes: 2332/2555 = 91%
   Primitives.lean::rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_copy: 699/767 = 91%
   Primitives.lean::splitCount_accept  reproduces  Catalog.lean::f2_splitCount_accept: 266/292 = 91%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedCut_count_run: 2197/2414 = 91%
   UniversalBlock.lean::universal_prepare_next  reproduces  Universal.lean::timedCut_prepare_next: 1959/2154 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Catalog.lean::f2_splitPoly_loop_end  reproduces  Primitives.lean::splitPoly_loop_end: 639/703 = 91%
   Primitives.lean::splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 605/666 = 91%
   UniversalBlock.lean::universal_live_block  reproduces  Universal.lean::timedCut_live_block: 5237/5766 = 91%
   Catalog.lean::rewind_heads  reproduces  Primitives.lean::catalogRewind: 395/435 = 91%
   Catalog.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Primitives.lean::splitEmit_separator  reproduces  Catalog.lean::f2_splitEmit_separator: 730/804 = 91%
   Catalog.lean::f2_loopHost_round  reproduces  Loop.lean::loopHost_round: 1989/2194 = 91%
   Nondeterminism.lean::e3_split_none_iff  reproduces  Nondeterminism.lean::certificateSplit_none_iff: 155/171 = 91%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Loop.lean::loopFuelCaptured_frame: 1423/1570 = 91%
   Primitives.lean::splitRestore_first  reproduces  Catalog.lean::f2_splitRestore_first: 608/671 = 91%
   Universal.lean::timed_universal_concrete  reproduces  Universal.lean::timed_universal: 384/424 = 91%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanStep_right: 143/158 = 91%
   Universal.lean::timed_pair_get  reproduces  UniversalStartup.lean::universal_pair_get: 257/284 = 90%
   Catalog.lean::f2_catalogPrefixTM_emit  reproduces  Primitives.lean::catalogPrefixTM_emit: 321/355 = 90%
   Catalog.lean::f2_splitSource_constant  reproduces  Primitives.lean::splitSource_constant: 424/469 = 90%
   Loop.lean::loopDebit_success  reproduces  Catalog.lean::f2_loopDebit_success: 141/156 = 90%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_initial_skip: 911/1008 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamRelease_step_right: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::transferTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::copyTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   UHaltMachine.lean::primrec_replicate_numOfString  reproduces  MathlibBridge.lean::codePrimBit: 156/173 = 90%
   Nondeterminism.lean::contSplitWord  reproduces  Nondeterminism.lean::e3SplitWord: 64/71 = 90%
   CertShell.lean::certSplitWord  reproduces  Nondeterminism.lean::e3SplitWord: 64/71 = 90%
   Primitives.lean::computesFunInTime_pairEncodeFixed  reproduces  Catalog.lean::computesFunInTime_pairEncodeFixed_spaceUsed: 91/101 = 90%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_initial: 263/292 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Primitives.lean::mapParse_block  reproduces  Primitives.lean::mapParse_first: 244/271 = 90%
   Primitives.lean::lenParse_run  reproduces  Catalog.lean::f2_lenParse_run: 1533/1703 = 90%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_initial_skip: 873/970 = 90%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Loop.lean::loopHost_fuel_copy: 1319/1466 = 90%
   Primitives.lean::catalogPoly_start  reproduces  Catalog.lean::f2_catalogPoly_start: 833/926 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Loop.lean::loopHost_borrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 489/544 = 90%
   Primitives.lean::splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_extra: 424/472 = 90%
   Catalog.lean::f2_splitBody_round  reproduces  Primitives.lean::splitBody_round: 4481/4991 = 90%
   Primitives.lean::lenParse_first  reproduces  Catalog.lean::f2_lenParse_first: 287/320 = 90%
   Catalog.lean::f2_splitScratch_erase  reproduces  Primitives.lean::splitScratch_erase: 139/155 = 90%
   Nondeterminism.lean::cont_choiceVerifier_mem_P  reproduces  Nondeterminism.lean::e3_verifier_of_split: 929/1036 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamRelease_step_right: 121/135 = 90%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_right: 121/135 = 90%
   Primitives.lean::splitSolve_source  reproduces  Catalog.lean::f2_splitSolve_source: 397/443 = 90%
   Primitives.lean::lenSuffix_run  reproduces  Primitives.lean::lenParse_first: 276/308 = 90%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Loop.lean::loopHost_anchor_return: 829/926 = 90%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_run: 627/701 = 89%
   Primitives.lean::splitBody_round  reproduces  Catalog.lean::f2_splitBody_round: 4481/5014 = 89%
   Catalog.lean::f2_exists_loopFind_space  reproduces  Loop.lean::exists_loopTM: 687/770 = 89%
   Primitives.lean::pairExtract_computes  reproduces  Catalog.lean::f2_pairExtract_computes: 443/497 = 89%
   Primitives.lean::catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_setup: 533/598 = 89%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopTM: 686/770 = 89%
   CodeFormat.lean::oneTapeFormat  reproduces  CodeFormat.lean::codeTable2Bits: 208/234 = 89%
   Catalog.lean::f2_loopReady  reproduces  Loop.lean::loopReady: 119/134 = 89%
   Primitives.lean::catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_emit: 468/527 = 89%
   Nondeterminism.lean::cont_parse_double  reproduces  Nondeterminism.lean::cont_parse_separator: 579/652 = 89%
   Catalog.lean::f2_splitRestore_append  reproduces  Primitives.lean::splitRestore_append: 1052/1185 = 89%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   MathlibBridge.lean::bridgeCfg_push  reproduces  MathlibBridge.lean::bridgeCfg_pop: 674/761 = 89%
   Universal.lean::timedCut_Interpreter_initialize  reproduces  UniversalInterpreter.lean::universalInterpreter_initialize: 1802/2036 = 89%
   Primitives.lean::lenSuffix_run  reproduces  Catalog.lean::f2_lenSuffix_run: 1436/1623 = 88%
   Nondeterminism.lean::a3n_eq_double  reproduces  Nondeterminism.lean::a3n_eq_separator: 1072/1212 = 88%
   Primitives.lean::rawStrip_computes  reproduces  Catalog.lean::f2_rawStrip_computes: 650/735 = 88%
   Catalog.lean::f2_pairDup_computes  reproduces  Primitives.lean::pairDup_computes: 1321/1494 = 88%
   Primitives.lean::splitCount_run  reproduces  Loop.lean::emCall_right_run: 152/172 = 88%
   Catalog.lean::f2_splitCount_run  reproduces  Loop.lean::emCall_right_run: 152/172 = 88%
   Loop.lean::loopDebit_value  reproduces  Catalog.lean::f2_loopDebit_value: 187/212 = 88%
   Primitives.lean::catalogBuffer_erase  reproduces  Loop.lean::emCall_erase_last: 118/134 = 88%
   Catalog.lean::f2_catalogBuffer_erase  reproduces  Loop.lean::emCall_erase_last: 118/134 = 88%
   Codes2Tape.lean::Code2TM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 206/234 = 88%
   Primitives.lean::pairValid_run  reproduces  Catalog.lean::f2_pairValid_run: 1083/1231 = 88%
   Catalog.lean::f2_scanStep_right  reproduces  Primitives.lean::scanStep_right: 139/158 = 88%
   Nondeterminism.lean::choiceCore_step  reproduces  Nondeterminism.lean::choiceCore_finish: 285/324 = 88%
   Primitives.lean::splitBody_prepare  reproduces  Primitives.lean::emitterP2_control: 73/83 = 88%
   Catalog.lean::f2_splitBody_prepare  reproduces  Primitives.lean::emitterP2_control: 73/83 = 88%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 551/627 = 88%
   UniversalStartup.lean::universalCapture_step  reproduces  Universal.lean::timedCapture_step: 1089/1241 = 88%
   Primitives.lean::catalogPrefixTM_emit  reproduces  Catalog.lean::f2_catalogPrefixTM_emit: 321/367 = 87%
   UniversalStartup.lean::universalCapture_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Universal.lean::timed_replay  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Universal.lean::timedCapture_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Loop.lean::emCall_right_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Catalog.lean::a2_mapSetup_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   SymbolLift.lean::Action.liftSymbols  reproduces  CounterLoop.lean::Action.mapWorkSymbols: 96/110 = 87%
   Primitives.lean::emitter_first_entry  reproduces  Primitives.lean::catalogFirstEntry: 327/375 = 87%
   Primitives.lean::emitter_first_entry  reproduces  Catalog.lean::f2_catalogFirstEntry: 327/375 = 87%
   Loop.lean::emCall_first_entry  reproduces  Primitives.lean::catalogFirstEntry: 327/375 = 87%
   Loop.lean::emCall_first_entry  reproduces  Catalog.lean::f2_catalogFirstEntry: 327/375 = 87%
   Primitives.lean::incFixed_computes  reproduces  Catalog.lean::f2_incFixed_computes: 2332/2675 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Primitives.lean::anyTrue_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 231/265 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   UniversalInterpreter.lean::universalInterpreter  reproduces  UniversalInterpreter.lean::universalSkipDone: 60/69 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Loop.lean::loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopFuelCaptured_frame: 1423/1639 = 87%
   UniversalStartup.lean::universalCapture_init  reproduces  Universal.lean::timedCapture_init: 276/318 = 87%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Nondeterminism.lean::b2_unary_run: 117/135 = 87%
   Catalog.lean::f2_loopBodySource_run  reproduces  Loop.lean::loopBodySource_run: 78/90 = 87%
   Catalog.lean::f2_loopHost_borrow_step  reproduces  Loop.lean::loopHost_borrow_step: 581/671 = 87%
   Primitives.lean::splitSource_constant  reproduces  Catalog.lean::f2_splitSource_constant: 424/490 = 87%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Primitives.lean::computesFunInTime_prepend: 122/141 = 87%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 661/764 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Nondeterminism.lean::e3SplitWord  reproduces  Nondeterminism.lean::contSplitWord: 64/74 = 86%
   Nondeterminism.lean::e3SplitWord  reproduces  CertShell.lean::certSplitWord: 64/74 = 86%
   Primitives.lean::splitPoly_loop_end  reproduces  Catalog.lean::f2_splitPoly_loop_end: 639/739 = 86%
   UniversalStartup.lean::universalCapture_run  reproduces  Universal.lean::timedCapture_run: 146/169 = 86%
   Universal.lean::timedCapture_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Loop.lean::loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 1319/1527 = 86%
   Primitives.lean::splitScratch_erase  reproduces  Catalog.lean::f2_splitScratch_erase: 139/161 = 86%
   CfgRecord.lean::recordStep_reject_run  reproduces  CfgRecord.lean::recordStep_empty_run: 467/541 = 86%
   Catalog.lean::f2_lenAction_apply  reproduces  Primitives.lean::lenAction_apply: 125/145 = 86%
   Loop.lean::loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_anchor_return: 829/963 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Catalog.lean::f2_strip_linear  reproduces  Primitives.lean::computesFunInTime_stripLast: 1616/1881 = 86%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_rewind: 1025/1195 = 86%
   Universal.lean::timedCut_live_block  reproduces  UniversalBlock.lean::universal_live_block: 5237/6108 = 86%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_pair_triple: 138/161 = 86%
   Primitives.lean::splitCount_run  reproduces  Universal.lean::timedFrame_run: 108/126 = 86%
   Catalog.lean::f2_splitCount_run  reproduces  Universal.lean::timedFrame_run: 108/126 = 86%
   Primitives.lean::emitterP2_update_right  reproduces  Primitives.lean::emitterP2_update_left: 542/633 = 86%
   UniversalInterpreter.lean::universalInterpreter_initialize  reproduces  Universal.lean::timedCut_Interpreter_initialize: 1802/2105 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_control: 71/83 = 86%
   Catalog.lean::f2_loopDebit_iterate_value  reproduces  Loop.lean::loopDebit_iterate_value: 248/290 = 86%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 661/773 = 86%
   Primitives.lean::splitStep_orbit  reproduces  Nondeterminism.lean::e3_step_orbit: 171/200 = 86%
   Catalog.lean::f2_splitStep_orbit  reproduces  Nondeterminism.lean::e3_step_orbit: 171/200 = 86%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedCapture_start: 434/508 = 85%
   CfgRecord.lean::recordStep_empty_run  reproduces  CfgRecord.lean::recordStep_reject_run: 467/547 = 85%
   Nondeterminism.lean::b2_ready_done  reproduces  Nondeterminism.lean::b2_ready_step: 539/632 = 85%
   Universal.lean::timedCapture_step  reproduces  Universal.lean::timedCapture_init: 271/318 = 85%
   CodeFormat.lean::oneTapeFormat  reproduces  CodeSimulator.lean::tableBitsK: 120/141 = 85%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::rawStrip_rewind: 599/704 = 85%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::rawStrip_rewind: 599/704 = 85%
   Nondeterminism.lean::e3_step_orbit  reproduces  Primitives.lean::splitStep_orbit: 171/201 = 85%
   Universal.lean::timedCapture_step  reproduces  UniversalStartup.lean::universalCapture_step: 1089/1281 = 85%
   Loop.lean::loopReady  reproduces  Catalog.lean::f2_loopReady: 119/140 = 85%
   Loop.lean::loopHost_fuel_setup  reproduces  Catalog.lean::f2_loopHost_fuel_setup: 782/921 = 85%
   Primitives.lean::splitSolve_of_body  reproduces  Nondeterminism.lean::e3_split_of_body: 796/938 = 85%
   CodeParser.lean::codeSkipAction  reproduces  CodeFormat.lean::codeSkipActionK: 106/125 = 85%
   Universal.lean::timedCapture_start  reproduces  UniversalStartup.lean::universalCapture_start: 434/512 = 85%
   Primitives.lean::scanStep_right  reproduces  Catalog.lean::f2_scanStep_right: 139/164 = 85%
   Nondeterminism.lean::e3_split_of_body  reproduces  Primitives.lean::splitSolve_of_body: 796/940 = 85%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanCopy_run: 408/482 = 85%
   Catalog.lean::f2_splitCount_apply  reproduces  Primitives.lean::splitCount_apply: 725/857 = 85%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_rewind_input: 1256/1488 = 84%
   Catalog.lean::f2_splitRestore_run  reproduces  Primitives.lean::splitRestore_run: 762/903 = 84%
   Catalog.lean::f2_loopHost_reject  reproduces  Loop.lean::loopHost_reject: 2023/2398 = 84%
   Primitives.lean::pairDup_computes  reproduces  Catalog.lean::f2_pairDup_computes: 1321/1566 = 84%
   Loop.lean::emCall_finalize_run  reproduces  Primitives.lean::emitterP2_control: 70/83 = 84%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 403/478 = 84%
   Primitives.lean::splitRestore_append  reproduces  Catalog.lean::f2_splitRestore_append: 1052/1248 = 84%
   Catalog.lean::f2_anyTrue_run  reproduces  Primitives.lean::anyTrue_run: 669/795 = 84%
   Nondeterminism.lean::cont_split_answer  reproduces  Nondeterminism.lean::e3_split_answer: 659/784 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   ChoiceWords.lean::expCertificateLength_strictMono  reproduces  ChoiceWords.lean::certificateLength_strictMono: 83/99 = 84%
   Nondeterminism.lean::e3_step_orbit  reproduces  Catalog.lean::f2_splitStep_orbit: 171/204 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_splitBody_count  reproduces  Primitives.lean::splitBody_count: 483/577 = 84%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_bank_final: 3070/3669 = 84%
   Primitives.lean::emitterP2_update_left  reproduces  Primitives.lean::emitterP2_update_right: 542/648 = 84%
   Catalog.lean::f2_loopHost_fuel_setup  reproduces  Loop.lean::loopHost_fuel_setup: 782/935 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Primitives.lean::emitterSplit_result  reproduces  Primitives.lean::splitLoop_result: 193/231 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Loop.lean::loopHost_fuel_return: 982/1176 = 84%
   CounterLoop.lean::Action.mapWorkSymbols  reproduces  SymbolLift.lean::Action.liftSymbols: 96/115 = 83%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 630/755 = 83%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::f2_splitBody_rewind  reproduces  Primitives.lean::splitBody_rewind: 447/538 = 83%
   Nondeterminism.lean::cont_parse_separator  reproduces  Nondeterminism.lean::cont_parse_double: 579/697 = 83%
   Catalog.lean::f2_loopCopy_initial  reproduces  Loop.lean::loopCopy_initial: 78/94 = 83%
   Catalog.lean::f2_splitBody_prepare  reproduces  Primitives.lean::splitBody_prepare: 1263/1523 = 83%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 587/708 = 83%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Nondeterminism.lean::a3n_eq_double: 1072/1293 = 83%
   Universal.lean::timedCut_skip_unary  reproduces  UniversalInterpreter.lean::universal_initial_skip: 802/970 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Universal.lean::timedCapture_init  reproduces  UniversalStartup.lean::universalCapture_init: 276/334 = 83%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 599/725 = 83%
   Catalog.lean::f2_splitSolve_closed  reproduces  Primitives.lean::splitSolve_closed: 323/391 = 83%
   Loop.lean::loopHost_borrow_step  reproduces  Catalog.lean::f2_loopHost_borrow_step: 581/704 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Loop.lean::exists_emitCallTM  reproduces  Loop.lean::exists_installCallTM: 194/236 = 82%
   Catalog.lean::f2_lenSuffix_run  reproduces  Primitives.lean::lenParse_first: 253/308 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Loop.lean::loopHost_contracts  reproduces  Catalog.lean::f2_loopHost_contracts: 3565/4347 = 82%
   Loop.lean::emCall_prepare_run  reproduces  Primitives.lean::emitterP2_control: 68/83 = 82%
   Loop.lean::emCall_bank_step  reproduces  Primitives.lean::emitterP2_control: 68/83 = 82%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_reject_run: 448/547 = 82%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::computesFunInTime_pairConcat: 125/153 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Catalog.lean::f2_loopHost_prepare  reproduces  Loop.lean::loopHost_prepare: 1091/1338 = 82%
   Catalog.lean::f2_catalogPolyMove_apply  reproduces  Primitives.lean::catalogPolyMove_apply: 141/173 = 82%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 615/755 = 81%
   Primitives.lean::emitterSplit_result  reproduces  Catalog.lean::f2_splitLoop_result: 193/237 = 81%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Catalog.lean::f2_splitEmbed_run: 153/188 = 81%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Loop.lean::loopBodySource_run  reproduces  Catalog.lean::f2_loopBodySource_run: 78/96 = 81%
   Catalog.lean::f2_loopControl_apply  reproduces  Loop.lean::loopControl_apply: 643/792 = 81%
   Catalog.lean::f2_splitBody_restore  reproduces  Primitives.lean::splitBody_restore: 405/499 = 81%
   Loop.lean::loopHost_reject  reproduces  Catalog.lean::f2_loopHost_reject: 2023/2493 = 81%
   Primitives.lean::catalogFirstEntry  reproduces  Primitives.lean::emitter_first_entry: 327/403 = 81%
   Primitives.lean::catalogFirstEntry  reproduces  Loop.lean::emCall_first_entry: 327/403 = 81%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Primitives.lean::emitter_first_entry: 327/403 = 81%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Loop.lean::emCall_first_entry: 327/403 = 81%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 557/687 = 81%
   Nondeterminism.lean::e3_verifier_of_split  reproduces  Nondeterminism.lean::cont_choiceVerifier_mem_P: 929/1146 = 81%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopTM: 624/770 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Loop.lean::loopValue_bits  reproduces  Nondeterminism.lean::a2Value_bits: 106/131 = 81%
   Catalog.lean::f2_loopValue_bits  reproduces  Nondeterminism.lean::a2Value_bits: 106/131 = 81%
   Primitives.lean::anyTrue_run  reproduces  Catalog.lean::f2_anyTrue_run: 669/828 = 81%
   Catalog.lean::f2_loopBorrow_run  reproduces  Nondeterminism.lean::a2Borrow_run: 353/437 = 81%
   Primitives.lean::splitBody_count  reproduces  Catalog.lean::f2_splitBody_count: 483/598 = 81%
   Primitives.lean::splitLoop_result  reproduces  Primitives.lean::emitterSplit_result: 193/239 = 81%
   Catalog.lean::f2_splitLoop_result  reproduces  Primitives.lean::emitterSplit_result: 193/239 = 81%
   Primitives.lean::splitBody_rewind  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::splitBody_restore  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::emitterP2_prepare_first  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::emitterP2_erase_first  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Catalog.lean::f2_splitBody_rewind  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Catalog.lean::f2_splitBody_restore  reproduces  Primitives.lean::emitterP2_control: 67/83 = 81%
   Primitives.lean::computesFunInTime_pairConcat  reproduces  Primitives.lean::computesFunInTime_pairSnd: 125/155 = 81%
   OracleNondeterministic.lean::OracleNDTM  reproduces  Oracle.lean::OracleTM: 141/175 = 81%
   Loop.lean::loopDebit_iterate_value  reproduces  Catalog.lean::f2_loopDebit_iterate_value: 248/308 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::extract_rewind: 599/746 = 80%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::extract_rewind: 599/746 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Universal.lean::timed_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Primitives.lean::splitCount_apply  reproduces  Catalog.lean::f2_splitCount_apply: 725/905 = 80%
   OracleSim.lean::oracleRestore_cell  reproduces  OracleSim.lean::oraclePrepare_zero: 112/140 = 80%
   Primitives.lean::splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_rewind: 447/559 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 630/790 = 80%
   OracleSim.lean::oracleMarkedCfg  reproduces  OracleSim.lean::oracleLocalCfg: 149/187 = 80%
   Primitives.lean::lenAction_apply  reproduces  Catalog.lean::f2_lenAction_apply: 125/157 = 80%
   UniversalBlock.lean::universal_skip_unary  reproduces  Universal.lean::timedCut_initial_skip: 802/1008 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Admin_apply: 210/264 = 80%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   Universal.lean::timedCut_Interpreter_first  reproduces  Universal.lean::timedCut_Admin_apply: 210/264 = 80%
   Loop.lean::emCall_right_scan  reproduces  Primitives.lean::emitterP2_control: 66/83 = 80%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Primitives.lean::emitterP2_control: 66/83 = 80%
   Primitives.lean::emitterAppend_run  reproduces  Catalog.lean::f2_scanCopy_run: 395/497 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Universal.lean::timedPrefix_complete  reproduces  Universal.lean::timedPrefix_penultimate: 318/401 = 79%
   Primitives.lean::extract_suffix  reproduces  Primitives.lean::extract_first: 226/285 = 79%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 615/776 = 79%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timed_clock_separator: 236/298 = 79%
   Primitives.lean::splitRestore_run  reproduces  Catalog.lean::f2_splitRestore_run: 762/963 = 79%
   Catalog.lean::f2_scanTrues_run  reproduces  Primitives.lean::scanStep_right: 125/158 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Primitives.lean::lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 253/320 = 79%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitPrepare_scan: 505/639 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_borrow_rewind: 932/1181 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_pairValid_block  reproduces  Primitives.lean::pairValid_block: 370/470 = 79%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_rewind_choices: 1256/1596 = 79%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 557/708 = 79%
   Primitives.lean::catalogPayload_computes  reproduces  Nondeterminism.lean::a3n_comp_at: 343/436 = 79%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Nondeterminism.lean::a2Value_bits  reproduces  Loop.lean::loopValue_bits: 106/135 = 79%
   Loop.lean::emCall_finish_final  reproduces  Loop.lean::emCall_finish_initial: 1279/1629 = 79%
   Nondeterminism.lean::e3_verifier_of_split  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::cont_choiceVerifier_mem_P  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::a2_exp_scheduler  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Primitives.lean::splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_prepare: 1263/1613 = 78%
   UHaltMachine.lean::primrec_replicate_numOfString  reproduces  MathlibBridge.lean::codePrimBitsNat: 101/129 = 78%
   UHaltMachine.lean::primrec_replicate_numOfString  reproduces  MathlibBridge.lean::bridgePrimNumber: 101/129 = 78%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 313/400 = 78%
   Universal.lean::timedCaptureTM  reproduces  UniversalStartup.lean::universalCaptureTM: 291/372 = 78%
   Loop.lean::exists_installCallTM  reproduces  Loop.lean::exists_emitCallTM: 194/248 = 78%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 599/767 = 78%
   Nondeterminism.lean::b2_rewind_step  reproduces  Nondeterminism.lean::b2_copy_done: 303/388 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Nondeterminism.lean::b2_unary_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 117/150 = 78%
   Loop.lean::loopCopy_initial  reproduces  Catalog.lean::f2_loopCopy_initial: 78/100 = 78%
   Nondeterminism.lean::a2Borrow_step  reproduces  Catalog.lean::f2_loopBorrow_step: 328/421 = 78%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_reject_run: 426/547 = 78%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 615/790 = 78%
   Primitives.lean::splitSolve_closed  reproduces  Catalog.lean::f2_splitSolve_closed: 323/415 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 549/708 = 78%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyTM: 369/476 = 78%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::clearTM_run_ofCfg: 310/400 = 78%
   Nondeterminism.lean::b2_copy_done  reproduces  Nondeterminism.lean::b2_rewind_step: 303/391 = 77%
   Primitives.lean::splitBody_restore  reproduces  Catalog.lean::f2_splitBody_restore: 405/523 = 77%
   MathlibBridge.lean::bridgeCfg_pop  reproduces  MathlibBridge.lean::bridgeCfg_push: 674/871 = 77%
   CodeFormat.lean::codeEraseActionK  reproduces  CodeFormat.lean::codeEraseWork: 167/216 = 77%
   Catalog.lean::f2_loopDebit_iterate_length  reproduces  Loop.lean::loopDebit_iterate_length: 68/88 = 77%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::scanStep_right: 122/158 = 77%
   Nondeterminism.lean::b2_host_bound  reproduces  Nondeterminism.lean::a2_host_bound: 381/494 = 77%
   Loop.lean::loopControl_apply  reproduces  Catalog.lean::f2_loopControl_apply: 643/834 = 77%
   Catalog.lean::f2_catalogPoly_advance  reproduces  Primitives.lean::catalogPoly_advance: 131/170 = 77%
   Nondeterminism.lean::b2_unary_run  reproduces  Universal.lean::timedFrame_run: 97/126 = 77%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_erase: 972/1264 = 77%
   Primitives.lean::splitLoop_bound  reproduces  Nondeterminism.lean::e3_loop_bound: 212/276 = 77%
   Nondeterminism.lean::e3_loop_bound  reproduces  Primitives.lean::splitLoop_bound: 212/276 = 77%
   Nondeterminism.lean::e3_loop_bound  reproduces  Catalog.lean::f2_splitLoop_bound: 212/276 = 77%
   Catalog.lean::f2_splitLoop_bound  reproduces  Nondeterminism.lean::e3_loop_bound: 212/276 = 77%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::a2_mapSetup_run: 125/163 = 77%
   Loop.lean::loopHost_halt_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 389/508 = 77%
   Nondeterminism.lean::b2_ready_run  reproduces  Nondeterminism.lean::b2_rewind_run: 196/256 = 77%
   Codes2Tape.lean::Code2TM.serialize  reproduces  UniversalInterpreter.lean::universalRecords: 160/209 = 77%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::emitterAppend_run: 408/533 = 77%
   Universal.lean::timedFive  reproduces  Universal.lean::timedSix: 78/102 = 76%
   Catalog.lean::f2_splitSolve_of_body  reproduces  Nondeterminism.lean::e3_split_of_body: 717/938 = 76%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 331/434 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Nondeterminism.lean::a2Buffer_write: 311/408 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Loop.lean::loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Primitives.lean::scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   Primitives.lean::catalogPolyMove_apply  reproduces  Catalog.lean::f2_catalogPolyMove_apply: 141/185 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Primitives.lean::emitterP2StateDecidableEq  reproduces  Primitives.lean::splitBodyStateDecidableEq: 408/537 = 76%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 587/773 = 76%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 329/434 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  UniversalStartup.lean::universalCapture_run: 128/169 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  Universal.lean::timedCapture_run: 128/169 = 76%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_initial: 221/292 = 76%
   Nondeterminism.lean::b2_guess_return  reproduces  Nondeterminism.lean::b2_initial: 221/292 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 615/814 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Primitives.lean::computesFunInTime_pairSnd  reproduces  Primitives.lean::computesFunInTime_pairFst: 117/155 = 75%
   Primitives.lean::computesFunInTime_pairFst  reproduces  Primitives.lean::computesFunInTime_pairSnd: 117/155 = 75%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 313/415 = 75%
   Loop.lean::exists_loopTM  reproduces  Loop.lean::exists_loopFindTM: 686/910 = 75%
   MathlibBridge.lean::bridgeCfg_push_input  reproduces  MathlibBridge.lean::bridgeCfg_pop_emit: 195/259 = 75%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   Codes2Tape.lean::exists_uniformMachineCode2  reproduces  EXPCOM.lean::exists_uniformMachineCode: 322/428 = 75%
   Nondeterminism.lean::a2Value_bits  reproduces  Catalog.lean::f2_loopValue_bits: 106/141 = 75%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::extract_replay_finish: 224/298 = 75%
   EXPCOM.lean::exists_uniformMachineCode  reproduces  Codes2Tape.lean::exists_uniformMachineCode2: 322/429 = 75%
   Primitives.lean::splitSolve_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 672/896 = 75%
   Catalog.lean::f2_pairValid_computes  reproduces  Primitives.lean::pairValid_computes: 216/288 = 75%
   UniversalInterpreter.lean::universalRecords  reproduces  UniversalBlock.lean::universalActions: 105/140 = 75%
   UniversalInterpreter.lean::universalRecords  reproduces  Universal.lean::timedCut_Actions: 105/140 = 75%
   Codes2Tape.lean::Code2TM.serialize  reproduces  UniversalBlock.lean::universalActions: 105/140 = 75%
   Codes2Tape.lean::Code2TM.serialize  reproduces  Universal.lean::timedCut_Actions: 105/140 = 75%
   CodeFormat.lean::oneTapeFormat  reproduces  UniversalBlock.lean::universalActions: 105/140 = 75%
   CodeFormat.lean::oneTapeFormat  reproduces  Universal.lean::timedCut_Actions: 105/140 = 75%
   CodeFormat.lean::codeTable2Bits  reproduces  UniversalBlock.lean::universalActions: 105/140 = 75%
   CodeFormat.lean::codeTable2Bits  reproduces  Universal.lean::timedCut_Actions: 105/140 = 75%
   Primitives.lean::splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_extra: 338/451 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Primitives.lean::pairValid_block  reproduces  Catalog.lean::f2_pairValid_block: 370/494 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   CodeFormat.lean::parseFull  reproduces  CodeFormat.lean::scan: 151/202 = 75%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 879/1176 = 75%
   Loop.lean::loopDebit_iterate_length  reproduces  Catalog.lean::f2_loopDebit_iterate_length: 68/91 = 75%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 236/316 = 75%
   Nondeterminism.lean::e3_split_answer  reproduces  Nondeterminism.lean::cont_split_answer: 659/883 = 75%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopFindTM: 679/910 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Catalog.lean::f2_loopBorrow_step  reproduces  Nondeterminism.lean::a2Borrow_step: 328/440 = 75%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timed_replay  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Oracle.lean::runFrom_plainEmptyOracle  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_ready_done: 539/724 = 74%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 879/1181 = 74%
   Nondeterminism.lean::a2Borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 353/476 = 74%
   Primitives.lean::emitterP2_body_length  reproduces  Primitives.lean::emitterP2_body_width: 493/665 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Universal.lean::timed_output_back  reproduces  Universal.lean::timed_clock_back: 401/541 = 74%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::emitterAppend_run: 395/533 = 74%
   Nondeterminism.lean::cont_core_run  reproduces  Seam.lean::seamRelease_step_right: 100/135 = 74%
   Nondeterminism.lean::cont_core_run  reproduces  Seam.lean::seamComp_step_right: 100/135 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Loop.lean::emCall_right_run  reproduces  UniversalStartup.lean::universalCapture_run: 125/169 = 74%
   Loop.lean::emCall_right_run  reproduces  Universal.lean::timedCapture_run: 125/169 = 74%
   Nondeterminism.lean::cont_core_run  reproduces  Catalog.lean::f2_splitEmbed_run: 139/188 = 74%
   UHaltMachine.lean::bits_foldr_bit_one  reproduces  MathlibBridge.lean::bridgeNumber_bits: 136/184 = 74%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_finish_final: 1279/1731 = 74%
   Universal.lean::timed_clock_back  reproduces  Universal.lean::timed_output_back: 401/543 = 74%
   Primitives.lean::extract_block  reproduces  Primitives.lean::extract_first: 210/285 = 74%
   Primitives.lean::splitLoop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 126/171 = 74%
   Catalog.lean::f2_splitLoop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 126/171 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Primitives.lean::emitterP2StateDecidableEq  reproduces  Catalog.lean::f2_splitBodyStateDecidableEq: 408/555 = 74%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Loop.lean::loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_halted_run: 484/659 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Oracle.lean::OracleTM  reproduces  OracleNondeterministic.lean::OracleNDTM: 141/192 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadWrite_sound: 143/195 = 73%
   Loop.lean::loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Loop.lean::loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Loop.lean::loopControlAction: 110/150 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::pairDupTM: 283/386 = 73%
   Primitives.lean::incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::pairDupTM: 283/386 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   OracleSim.lean::oracleRestore_cell  reproduces  OracleSim.lean::oraclePrepare_tail: 101/138 = 73%
   OracleSim.lean::oraclePrepare_zero  reproduces  OracleSim.lean::oraclePrepare_tail: 101/138 = 73%
   MathlibBridge.lean::CodeFormat.primrec_scan  reproduces  MathlibBridge.lean::codePrimSkipFin: 188/257 = 73%
   Primitives.lean::emitterP2_body_width  reproduces  Primitives.lean::emitterP2_body_length: 493/674 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState: 76/104 = 73%
   CfgRecord.lean::recordStep_map_snapshot  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 875/1198 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Nondeterminism.lean::a2Buffer_read: 65/89 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Loop.lean::loopBuffer_read: 65/89 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Universal.lean::timedFrame_run: 92/126 = 73%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalBlock.lean::universal_skip_unary: 873/1196 = 73%
   Primitives.lean::mapStart  reproduces  Primitives.lean::lenStart: 1210/1659 = 73%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Interpreter_first: 210/288 = 73%
   Universal.lean::timedCut_Admin_apply  reproduces  Universal.lean::timedCut_Interpreter_first: 210/288 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   Universal.lean::timedCanon_complete  reproduces  UniversalStartup.lean::universalCanon_complete: 287/394 = 73%
   UniversalInterpreter.lean::universal_serialization_header  reproduces  UniversalBlock.lean::universal_serialization_actions: 589/809 = 73%
   UniversalInterpreter.lean::universal_serialization_header  reproduces  Universal.lean::timedCut_serialization_actions: 589/809 = 73%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 706/970 = 73%
   Loop.lean::loopHost_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1091/1499 = 73%
   Primitives.lean::splitCount_run  reproduces  UniversalStartup.lean::universalCapture_run: 123/169 = 73%
   Primitives.lean::splitCount_run  reproduces  Universal.lean::timedCapture_run: 123/169 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  UniversalStartup.lean::universalCapture_run: 123/169 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Universal.lean::timedCapture_run: 123/169 = 73%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 500/687 = 73%
   MathlibBridge.lean::bridgeNumber_bits  reproduces  UHaltMachine.lean::bits_foldr_bit_one: 136/187 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Universal.lean::timedCapture_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Loop.lean::emCall_right_run: 125/172 = 73%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_skip_unary: 911/1254 = 73%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferTM: 369/508 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Universal.lean::timedCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Loop.lean::emCall_right_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   OracleSim.lean::oracleRestore_zero  reproduces  OracleSim.lean::oracleRestore_three: 74/102 = 73%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Primitives.lean::catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_emit: 366/506 = 72%
   Loop.lean::loopHost_start  reproduces  Catalog.lean::f2_loopHost_start: 209/289 = 72%
   Primitives.lean::splitRestore_append  reproduces  Primitives.lean::splitPrepare_extra: 326/451 = 72%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 496/687 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  UniversalStartup.lean::universalCapture_run: 122/169 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Universal.lean::timedCapture_run: 122/169 = 72%
   Universal.lean::timed_clock_get  reproduces  UniversalStartup.lean::universal_pair_get: 205/284 = 72%
   OracleSim.lean::oraclePrepare_tail  reproduces  OracleSim.lean::oraclePrepare_zero: 101/140 = 72%
   Nondeterminism.lean::a2Buffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Loop.lean::loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Primitives.lean::catalogPoly_advance  reproduces  Catalog.lean::f2_catalogPoly_advance: 131/182 = 72%
   Primitives.lean::emitterSplit_find  reproduces  Nondeterminism.lean::e3_find_eq: 123/171 = 72%
   Nondeterminism.lean::b2_ready_done  reproduces  Nondeterminism.lean::b2_initial: 210/292 = 72%
   Universal.lean::timedBorrow_length  reproduces  Universal.lean::timedBorrow_fold: 64/89 = 72%
   Primitives.lean::emitterP2_erase_back  reproduces  Nondeterminism.lean::a2Buffer_read: 64/89 = 72%
   Primitives.lean::emitterP2_erase_back  reproduces  Loop.lean::loopBuffer_read: 64/89 = 72%
   Primitives.lean::emitterP2_erase_back  reproduces  Catalog.lean::f2_loopBuffer_read: 64/89 = 72%
   Loop.lean::loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_return: 982/1366 = 72%
   Nondeterminism.lean::a2_load_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 549/764 = 72%
   Universal.lean::timedFrame_run  reproduces  Nondeterminism.lean::b2_unary_run: 97/135 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 227/316 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 706/987 = 72%
   OracleNondeterministic.lean::stepWith  reproduces  Oracle.lean::step: 118/165 = 72%
   Primitives.lean::emitterSplit_of_body  reproduces  Primitives.lean::splitSolve_of_body: 672/940 = 71%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_unary_copy: 704/985 = 71%
   Primitives.lean::splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Oracle.lean::runFrom_ofMultiTapeTM  reproduces  Catalog.lean::a2_mapSetup_heads: 70/98 = 71%
   Loop.lean::loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Loop.lean::loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Loop.lean::loop_find_run: 484/678 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Primitives.lean::splitFind_eq  reproduces  Nondeterminism.lean::e3_find_eq: 122/171 = 71%
   Catalog.lean::f2_splitFind_eq  reproduces  Nondeterminism.lean::e3_find_eq: 122/171 = 71%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_arg: 1025/1438 = 71%
   Catalog.lean::f2_loopReady_call  reproduces  Loop.lean::loopReady_call: 708/994 = 71%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 225/316 = 71%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 225/316 = 71%
   Nondeterminism.lean::choice_certificate_iff  reproduces  Nondeterminism.lean::e3_choice_certificate: 158/222 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   CodeSimulator.lean::h1Round_payload  reproduces  CodeSimulator.lean::h1Data_shift: 142/200 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_counterInc_bits  reproduces  Nondeterminism.lean::a2Value_bits: 93/131 = 71%
   Nondeterminism.lean::NP_eq_iUnion_NTIME  reproduces  Nondeterminism.lean::NEXP_eq_iUnion_NTIME: 66/93 = 71%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Loop.lean::emCall_right_run: 122/172 = 71%
   Catalog.lean::a2_mapVirtual_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 190/268 = 71%
   Primitives.lean::extract_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 224/316 = 71%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::emitterP2_erase_scan: 224/316 = 71%
   Nondeterminism.lean::e3_split_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 635/896 = 71%
   RecordTable.lean::rt_copyState_decidableEq  reproduces  RecordTable.lean::rt_copyState_fintype: 92/130 = 71%
   Primitives.lean::rawStripTM  reproduces  Loop.lean::loopReplayTM: 92/130 = 71%
   Primitives.lean::rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Loop.lean::loopReplayTM: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Primitives.lean::pairValid_computes  reproduces  Catalog.lean::f2_pairValid_computes: 216/306 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   Primitives.lean::lenStart  reproduces  Nondeterminism.lean::cont_pair_empty: 103/146 = 71%
   Catalog.lean::f2_lenStart  reproduces  Nondeterminism.lean::cont_pair_empty: 103/146 = 71%
   Catalog.lean::f2_extract_replay  reproduces  Primitives.lean::extract_replay_finish: 210/298 = 70%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Nondeterminism.lean::NEXP_eq_iUnion_NTIME  reproduces  Nondeterminism.lean::NP_eq_iUnion_NTIME: 66/94 = 70%
   Primitives.lean::splitRestoreTM  reproduces  Primitives.lean::splitPrepareTM: 280/399 = 70%
   Primitives.lean::splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Primitives.lean::splitPrepareTM: 280/399 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::extract_replay_finish: 209/298 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Loop.lean::loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 932/1329 = 70%
   Primitives.lean::splitRestoreScan  reproduces  Primitives.lean::splitPrepareScan: 68/97 = 70%
   Catalog.lean::f2_splitRestoreScan  reproduces  Primitives.lean::splitPrepareScan: 68/97 = 70%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadSign_sound: 159/227 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_reject_run: 383/547 = 70%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_transfer_trace: 1160/1657 = 70%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_inverse: 128/183 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_rewind: 835/1195 = 70%
   Nondeterminism.lean::a3n_scaled_envelope  reproduces  Nondeterminism.lean::a2_envelope: 535/766 = 70%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedCut_initial_skip: 704/1008 = 70%
   Loop.lean::loopDebit  reproduces  Nondeterminism.lean::a2Debit: 62/89 = 70%
   Catalog.lean::f2_loopDebit  reproduces  Nondeterminism.lean::a2Debit: 62/89 = 70%
   UniversalInterpreter.lean::universal_record_shape  reproduces  UniversalBlock.lean::universalActionBits_decode: 133/191 = 70%
   UniversalInterpreter.lean::universal_record_shape  reproduces  Universal.lean::timedCut_ActionBits_decode: 133/191 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   UniversalInterpreter.lean::universalEval_step  reproduces  Universal.lean::timedCut_Eval_step: 138/199 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::emitterToken_double: 543/785 = 69%
   CfgRecord.lean::recordStep_probe_run  reproduces  CfgRecord.lean::recordStep_read_run: 103/149 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Loop.lean::loopBody_step  reproduces  Loop.lean::loopBody_stop: 239/346 = 69%
   Nondeterminism.lean::cont_start_core  reproduces  Nondeterminism.lean::cont_write_apply: 221/320 = 69%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterP2_erase_scan: 218/316 = 69%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterP2_erase_scan: 218/316 = 69%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::scanStep_right: 109/158 = 69%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Primitives.lean::scanStep_right: 109/158 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Primitives.lean::emitterTokenTM  reproduces  Primitives.lean::pairDupTM: 266/386 = 69%
   Primitives.lean::emitterTokenTM  reproduces  Catalog.lean::f2_pairDupTM: 266/386 = 69%
   Primitives.lean::splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Primitives.lean::splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamRelease_step_right: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   Catalog.lean::f2_counterInc_bits  reproduces  Loop.lean::loopValue_bits: 93/135 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   Universal.lean::timed_replay  reproduces  Catalog.lean::a2_mapSetup_run: 112/163 = 69%
   Primitives.lean::emitterP2_erase_run  reproduces  Primitives.lean::emitterP2_erase_scan: 217/316 = 69%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::emitterP2_erase_scan: 217/316 = 69%
   Universal.lean::timedCut_Eval_step  reproduces  UniversalInterpreter.lean::universalEval_step: 138/201 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Loop.lean::loopDebit_value  reproduces  Nondeterminism.lean::a2Debit_value: 128/187 = 68%
   Catalog.lean::f2_loopDebit_value  reproduces  Nondeterminism.lean::a2Debit_value: 128/187 = 68%
   Universal.lean::timedBorrow_value  reproduces  Universal.lean::timedBorrow_underflow: 91/133 = 68%
   Loop.lean::loopHost_init  reproduces  Catalog.lean::f2_loopHost_init: 65/95 = 68%
   Primitives.lean::extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 210/307 = 68%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_empty_run: 370/541 = 68%
   Primitives.lean::rawStripTM  reproduces  Primitives.lean::emitterP2EraseTM: 188/275 = 68%
   Catalog.lean::f2_rawStripTM  reproduces  Primitives.lean::emitterP2EraseTM: 188/275 = 68%
   Nondeterminism.lean::cont_parse_run  reproduces  Nondeterminism.lean::a3n_eq_parse: 350/512 = 68%
   CodeParser.lean::codeReadSign_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 159/233 = 68%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_unary_copy: 673/987 = 68%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   UniversalStartup.lean::universalCapture_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Universal.lean::timed_replay  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Universal.lean::timedCapture_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Primitives.lean::splitCount_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Loop.lean::emCall_right_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Catalog.lean::f2_splitCount_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Catalog.lean::a2_mapSetup_run  reproduces  Nondeterminism.lean::b2_unary_run: 92/135 = 68%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_unary_copy: 671/985 = 68%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::extract_replay_finish: 203/298 = 68%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::extract_replay_finish: 203/298 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   Catalog.lean::f2_loopHost_input_rewind  reproduces  Loop.lean::loopHost_input_rewind: 164/241 = 68%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairConcat: 104/153 = 68%
   Catalog.lean::f2_splitRestore_append  reproduces  Primitives.lean::splitPrepare_extra: 306/451 = 68%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_right_frame: 192/283 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedCut_live_before: 82/121 = 68%
   Universal.lean::timedCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Universal.lean::timedCapture_start  reproduces  Universal.lean::timedCut_live_before: 82/121 = 68%
   Catalog.lean::skipBackTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 969/1430 = 68%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairSnd: 105/155 = 68%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairFst: 105/155 = 68%
   RecordTable.lean::rt_find_scan_phase  reproduces  RecordTable.lean::rt_find_skip_phase: 344/508 = 68%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimUnary: 367/542 = 68%
   Primitives.lean::emitterSplit_of_body  reproduces  Nondeterminism.lean::e3_split_of_body: 635/938 = 68%
   Catalog.lean::f2_splitRestore_scan  reproduces  Primitives.lean::splitPrepare_scan: 432/639 = 68%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_arg: 972/1438 = 68%
   Primitives.lean::mapStart  reproduces  Catalog.lean::f2_lenStart: 1149/1701 = 68%
   CodeFormat.lean::codeSkipActionK  reproduces  CodeParser.lean::codeSkipAction: 106/157 = 68%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::a2_mapSetup_run: 110/163 = 67%
   Oracle.lean::step  reproduces  OracleNondeterministic.lean::stepWith: 118/175 = 67%
   CodeFormat.lean::codeTable2Bits  reproduces  CodeSimulator.lean::tableBitsK: 95/141 = 67%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_initial_skip: 678/1008 = 67%
   MathlibBridge.lean::codePrimSkipTable1  reproduces  MathlibBridge.lean::codePrimSkipTable2: 135/201 = 67%
   Primitives.lean::rawStrip_replay  reproduces  Primitives.lean::extract_replay: 390/581 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Primitives.lean::extract_replay: 390/581 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::scanStep_right: 106/158 = 67%
   Universal.lean::timedCut_initial_skip  reproduces  UniversalBlock.lean::universal_skip_unary: 802/1196 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_initial_skip: 675/1008 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Loop.lean::loopHost_input_rewind  reproduces  Catalog.lean::f2_loopHost_input_rewind: 164/245 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::emitterAppend_run: 356/533 = 67%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_right_frame: 189/283 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Primitives.lean::emitterP2_body_prepare  reproduces  Primitives.lean::emitterP2_body_compare: 566/849 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Universal.lean::timed_clock_separator  reproduces  UniversalStartup.lean::universal_pair_separator: 138/207 = 67%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timed_pair_separator: 138/207 = 67%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_inverse: 122/183 = 67%
   Universal.lean::timed_replay  reproduces  Seam.lean::seamCompTM_runFrom_left: 112/168 = 67%
   RecordTable.lean::rt_copyState_fintype  reproduces  RecordTable.lean::rt_copyState_decidableEq: 92/138 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Universal.lean::timedBorrow_fold  reproduces  Universal.lean::timedBorrow_length: 64/96 = 67%
   Nondeterminism.lean::a2Debit  reproduces  Loop.lean::loopDebit: 62/93 = 67%
   Catalog.lean::f2_loopDebit  reproduces  Loop.lean::loopDebit: 62/93 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Nondeterminism.lean::b2_guess_run  reproduces  Nondeterminism.lean::cont_guess_run: 151/227 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::rawStrip_replay: 270/406 = 67%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::emitterTokenTM: 266/400 = 66%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::emitterTokenTM: 266/400 = 66%
   Primitives.lean::catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Catalog.lean::rewind_heads: 395/594 = 66%
   Primitives.lean::scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   CodeFormat.lean::codeTable2Bits  reproduces  Codes2Tape.lean::Code2TM.serialize: 206/310 = 66%
   Nondeterminism.lean::b2_rewind_run  reproduces  Nondeterminism.lean::b2_ready_run: 196/295 = 66%
   Primitives.lean::rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 390/587 = 66%
   Loop.lean::loopReady_call  reproduces  Catalog.lean::f2_loopReady_call: 708/1066 = 66%
   CodeParser.lean::codeBitsNat_bits  reproduces  Nondeterminism.lean::a2Value_bits: 87/131 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Universal.lean::timedCut_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 644/970 = 66%
   Loop.lean::emCall_track_action  reproduces  Universal.lean::timedCapture_init: 211/318 = 66%
   Universal.lean::timed_replay  reproduces  UniversalStartup.lean::universalCapture_run: 112/169 = 66%
   Universal.lean::timed_replay  reproduces  Universal.lean::timedCapture_run: 112/169 = 66%
   OracleSim.lean::oraclePrepare  reproduces  OracleSim.lean::oracleErase_step: 143/216 = 66%
   Catalog.lean::f2_splitSolve_of_body  reproduces  Primitives.lean::emitterSplit_of_body: 593/896 = 66%
   Primitives.lean::rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 203/307 = 66%
   Nondeterminism.lean::e3_choice_certificate  reproduces  Nondeterminism.lean::choice_certificate_iff: 158/239 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Loop.lean::loop_run  reproduces  Loop.lean::loop_find_run: 448/678 = 66%
   Loop.lean::loop_run  reproduces  Catalog.lean::f2_loop_find_run: 448/678 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Loop.lean::emCall_finish_rewind  reproduces  Loop.lean::emCall_finish_erase: 835/1264 = 66%
   Primitives.lean::splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 68/103 = 66%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalInterpreter.lean::universal_initial_skip: 640/970 = 66%
   Primitives.lean::splitSolve_of_body  reproduces  Catalog.lean::f2_splitSolve_of_body: 886/1343 = 66%
   Primitives.lean::emitterP2_pair_frame  reproduces  Primitives.lean::emitterP2_left_frame: 186/282 = 66%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::splitRewindTM: 122/185 = 66%
   Primitives.lean::incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Catalog.lean::f2_loopBody_step  reproduces  Loop.lean::loopBody_stop: 228/346 = 66%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 637/970 = 66%
   Catalog.lean::f2_loopHost_init  reproduces  Loop.lean::loopHost_init: 65/99 = 66%
   CfgRecord.lean::recordStep_halt_run  reproduces  CfgRecord.lean::recordStep_empty_run: 355/541 = 66%
   Primitives.lean::extract_run  reproduces  Primitives.lean::lenParse_run: 1077/1643 = 66%
   Universal.lean::timedFrame_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 110/168 = 65%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 500/764 = 65%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::extract_replay_finish: 195/298 = 65%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_unary_copy: 644/985 = 65%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::rawStrip_rewind: 460/704 = 65%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::rawStrip_rewind: 460/704 = 65%
   Universal.lean::timedPrefix_live  reproduces  UniversalStartup.lean::universal_live_before: 79/121 = 65%
   Universal.lean::timedPrefix_live  reproduces  Universal.lean::timedCut_live_before: 79/121 = 65%
   Catalog.lean::f2_catalogPair_inverse  reproduces  Nondeterminism.lean::a3n_pair_inverse: 220/337 = 65%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_empty_run: 353/541 = 65%
   Universal.lean::timedCut_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 644/987 = 65%
   Loop.lean::emCall_triple_other  reproduces  Loop.lean::emCall_triple_pair: 152/233 = 65%
   Universal.lean::timed_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 135/207 = 65%
   Universal.lean::timed_pair_get  reproduces  Universal.lean::timed_pair_separator: 135/207 = 65%
   Nondeterminism.lean::b2_unary_step  reproduces  Seam.lean::seamRelease_step_right: 88/135 = 65%
   Nondeterminism.lean::b2_unary_step  reproduces  Seam.lean::seamComp_step_right: 88/135 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Universal.lean::timed_replay  reproduces  Loop.lean::emCall_right_run: 112/172 = 65%
   Universal.lean::timedFrame_run  reproduces  UniversalStartup.lean::universalCapture_run: 110/169 = 65%
   Universal.lean::timedFrame_run  reproduces  Universal.lean::timedCapture_run: 110/169 = 65%
   Primitives.lean::extract_suffix  reproduces  Primitives.lean::scanCopy_suffix: 553/850 = 65%
   Catalog.lean::f2_extract_suffix  reproduces  Primitives.lean::scanCopy_suffix: 553/850 = 65%
   Universal.lean::timedPrefix_code  reproduces  Universal.lean::timedPrefix_complete: 507/780 = 65%
   Nondeterminism.lean::a2Debit_value  reproduces  Loop.lean::loopDebit_value: 128/197 = 65%
   Loop.lean::loopBodyImage  reproduces  Loop.lean::emLoopCall: 87/134 = 65%
   Primitives.lean::lenStart  reproduces  Primitives.lean::mapStart: 1210/1864 = 65%
   Primitives.lean::emitterP2_small_frame  reproduces  Primitives.lean::emitterP2_left_frame: 183/282 = 65%
   Seam.lean::seamRelease_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Primitives.lean::splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 432/666 = 65%
   Catalog.lean::clearTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 310/478 = 65%
   Primitives.lean::splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 306/472 = 65%
   Nondeterminism.lean::a2_host_bound  reproduces  Nondeterminism.lean::b2_host_bound: 381/588 = 65%
   Loop.lean::loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 228/352 = 65%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 171/264 = 65%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Admin_apply: 171/264 = 65%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_right_step: 134/207 = 65%
   Primitives.lean::scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 106/164 = 65%
   Catalog.lean::f2_loopCall_reframe  reproduces  Loop.lean::loopCall_reframe: 484/749 = 65%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::scanStep_right: 102/158 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   CodeFormat.lean::scan  reproduces  CodeFormat.lean::parseFull: 151/234 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_stamp: 450/698 = 64%
   CodeParser.lean::codeBitsNat_bits  reproduces  Loop.lean::loopValue_bits: 87/135 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Primitives.lean::splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_extract_run  reproduces  Primitives.lean::lenParse_run: 1057/1643 = 64%
   Primitives.lean::splitBody_rewind  reproduces  Primitives.lean::splitBody_restore: 321/499 = 64%
   Scan.lean::writeConstTM_run_ofCfg  reproduces  Scan.lean::inputCopyTM_run_ofCfg: 265/412 = 64%
   CodeSimulator.lean::binaryGuard_escape  reproduces  CodeSimulator.lean::binaryGuard_done: 922/1434 = 64%
   Catalog.lean::f2_loopHost_release  reproduces  Loop.lean::loopHost_release: 524/815 = 64%
   Nondeterminism.lean::cont_split_length  reproduces  Nondeterminism.lean::e3_split_length: 90/140 = 64%
   Loop.lean::loopBody_run  reproduces  Universal.lean::timedFrame_run: 81/126 = 64%
   Catalog.lean::f2_loopBody_run  reproduces  Universal.lean::timedFrame_run: 81/126 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_pair_separator: 133/207 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 496/773 = 64%
   Primitives.lean::splitPrepareScan  reproduces  Primitives.lean::splitRestoreScan: 68/106 = 64%
   Catalog.lean::f2_splitPrepareScan  reproduces  Primitives.lean::splitRestoreScan: 68/106 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   Primitives.lean::emitter_bits_injective  reproduces  Nondeterminism.lean::a2Value_bits: 84/131 = 64%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Nondeterminism.lean::a2Value_bits: 84/131 = 64%
   CodeFormat.lean::oneTapeFormat  reproduces  UniversalInterpreter.lean::universalRecords: 134/209 = 64%
   CodeFormat.lean::codeTable2Bits  reproduces  UniversalInterpreter.lean::universalRecords: 134/209 = 64%
   Primitives.lean::catalogPoly_emit  reproduces  Primitives.lean::catalogPoly_setup: 366/571 = 64%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_write_apply: 205/320 = 64%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_write_apply: 205/320 = 64%
   Nondeterminism.lean::e3ChoiceVerifier  reproduces  OracleNondeterministic.lean::AcceptsWithin: 71/111 = 64%
   Nondeterminism.lean::choiceVerifier  reproduces  OracleNondeterministic.lean::AcceptsWithin: 71/111 = 64%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_skip_unary: 802/1254 = 64%
   Universal.lean::timedFrame_run  reproduces  Loop.lean::emCall_right_run: 110/172 = 64%
   Loop.lean::loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   Catalog.lean::f2_loop_find_run  reproduces  Loop.lean::loop_run: 448/701 = 64%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedCut_initial_skip: 644/1008 = 64%
   ChoiceWords.lean::certificateLength_strictMono  reproduces  ChoiceWords.lean::expCertificateLength_strictMono: 83/130 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::rawStrip_replay: 259/406 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Primitives.lean::extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Primitives.lean::lenSuffix_run  reproduces  Primitives.lean::anyTrue_run: 506/795 = 64%
   Catalog.lean::f2_lenSuffix_run  reproduces  Primitives.lean::anyTrue_run: 506/795 = 64%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 168/264 = 64%
   UniversalBlock.lean::universal_apply_record  reproduces  Universal.lean::timedCut_Admin_apply: 168/264 = 64%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 168/264 = 64%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Admin_apply: 168/264 = 64%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 201/316 = 64%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timedClockPrefix_length: 89/140 = 64%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 195/307 = 64%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::rawStrip_rewind: 447/704 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::rawStrip_rewind: 447/704 = 63%
   Universal.lean::timed_output_step  reproduces  Universal.lean::timedClock_step: 158/249 = 63%
   Catalog.lean::a2_loop_prepare  reproduces  Loop.lean::loopHost_prepare: 849/1338 = 63%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_copy_trace: 793/1250 = 63%
   Primitives.lean::emitterP2_body_compare  reproduces  Primitives.lean::emitterP2_body_prepare: 566/894 = 63%
   Catalog.lean::f2_incFixed_computes  reproduces  Primitives.lean::scanStep_right: 100/158 = 63%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::scanCopy_run: 305/482 = 63%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::splitPrepare_rewind: 477/755 = 63%
   Loop.lean::emCall_track_action  reproduces  UniversalStartup.lean::universalCapture_init: 211/334 = 63%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::extract_replay_finish: 188/298 = 63%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::extract_replay_finish: 188/298 = 63%
   Primitives.lean::pairExtractTM  reproduces  Loop.lean::loopReplayTM: 82/130 = 63%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Nondeterminism.lean::a3n_unpad_EXP  reproduces  ChoiceWords.lean::expCertificateLength_strictMono: 82/130 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Loop.lean::loopReplayTM: 82/130 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::splitPrepare_rewind: 476/755 = 63%
   Nondeterminism.lean::a3n_eq_scan  reproduces  Primitives.lean::emitterP2_erase_scan: 199/316 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::inputFoldTM_run_ofCfg: 202/321 = 63%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 259/412 = 63%
   Scan.lean::inputCopyTM_run_ofCfg  reproduces  Scan.lean::writeConstTM_run_ofCfg: 265/422 = 63%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::rawStrip_rewind: 442/704 = 63%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::rawStrip_rewind: 442/704 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::splitRewindTM: 116/185 = 63%
   Primitives.lean::pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::splitRewindTM: 116/185 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timed_pair_get: 173/276 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   Nondeterminism.lean::a2Debit  reproduces  Catalog.lean::f2_loopDebit: 62/99 = 63%
   Loop.lean::loopDebit  reproduces  Catalog.lean::f2_loopDebit: 62/99 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timed_clock_get: 236/377 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::rawStrip_replay: 254/406 = 63%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::rawStrip_replay: 254/406 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Universal.lean::timedCanon_run  reproduces  UniversalStartup.lean::universalCanon_run: 187/300 = 62%
   Loop.lean::loopHost_borrow_run  reproduces  Nondeterminism.lean::a2Borrow_run: 272/437 = 62%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Nondeterminism.lean::a2Borrow_run: 272/437 = 62%
   Primitives.lean::emitter_bits_injective  reproduces  Loop.lean::loopValue_bits: 84/135 = 62%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Loop.lean::loopValue_bits: 84/135 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Primitives.lean::pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 102/164 = 62%
   Loop.lean::loopBodyDispatch  reproduces  Loop.lean::loopBodyImage: 118/190 = 62%
   Loop.lean::loopBody_stop  reproduces  Universal.lean::timedCapture_transfer: 77/124 = 62%
   Catalog.lean::f2_loopBody_stop  reproduces  Universal.lean::timedCapture_transfer: 77/124 = 62%
   Primitives.lean::extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1057/1703 = 62%
   UniversalBlock.lean::universal_skip_unary  reproduces  Universal.lean::timedCut_unary_copy: 611/985 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   CodeFormat.lean::oneTapeFormat  reproduces  Codes2Tape.lean::Code2TM.serialize: 192/310 = 62%
   Universal.lean::timedCut_skip_unary  reproduces  UniversalInterpreter.lean::universal_unary_copy: 611/987 = 62%
   Primitives.lean::lenCfg  reproduces  Primitives.lean::mapCfg: 99/160 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Primitives.lean::pairExtractTM  reproduces  Primitives.lean::rawStripTM: 285/461 = 62%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Primitives.lean::rawStripTM: 285/461 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::extract_rewind: 461/746 = 62%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::extract_rewind: 461/746 = 62%
   CodeParser.lean::codeBitsNat_bits  reproduces  Catalog.lean::f2_loopValue_bits: 87/141 = 62%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 447/725 = 62%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 254/412 = 62%
   Primitives.lean::mapStart  reproduces  Nondeterminism.lean::cont_pair_empty: 90/146 = 62%
   Catalog.lean::f2_lenStart  reproduces  Primitives.lean::mapStart: 1149/1864 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   CodeFormat.lean::actionBits₂  reproduces  CodeFormat.lean::actionBitsK: 93/151 = 62%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Catalog.lean::f2_splitPrepare_rewind: 477/776 = 61%
   Nondeterminism.lean::b2_copy_step  reproduces  Nondeterminism.lean::a2_copy_step: 325/529 = 61%
   Catalog.lean::f2_extract_suffix  reproduces  Primitives.lean::extract_first: 175/285 = 61%
   CodeParser.lean::codeReadWrite_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 143/233 = 61%
   Primitives.lean::lenParse_block  reproduces  Primitives.lean::lenParse_first: 189/308 = 61%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Catalog.lean::f2_splitPrepare_rewind: 476/776 = 61%
   Loop.lean::loopHost_fuel_return  reproduces  Loop.lean::loopHost_payload_scan: 422/688 = 61%
   UniversalStartup.lean::universalCapture_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Universal.lean::timed_replay  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Universal.lean::timedFrame_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Universal.lean::timedCapture_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Primitives.lean::splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Loop.lean::emCall_right_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::f2_splitCount_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Catalog.lean::a2_mapSetup_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Loop.lean::loopFuel_init  reproduces  Universal.lean::timedCapture_init: 195/318 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Universal.lean::timedCapture_init: 195/318 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 188/307 = 61%
   Primitives.lean::lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 506/828 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamRelease_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Loop.lean::emCall_clear_scan  reproduces  Primitives.lean::emitterP2_erase_scan: 193/316 = 61%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 461/755 = 61%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 461/755 = 61%
   Primitives.lean::incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 100/164 = 61%
   Primitives.lean::emitterAppend_run  reproduces  Catalog.lean::f2_scanStep_right: 100/164 = 61%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Nondeterminism.lean::a3n_pair_inverse  reproduces  Catalog.lean::f2_catalogPair_inverse: 220/361 = 61%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 460/755 = 61%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 460/755 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Primitives.lean::splitPrepare_scan  reproduces  Primitives.lean::splitRestore_scan: 505/831 = 61%
   Primitives.lean::splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 68/112 = 61%
   OracleNondeterministic.lean::runWith_headBlank  reproduces  OracleNondeterministic.lean::OracleNDTM.stepWith_eq_of_ne_qQuery: 83/137 = 61%
   Loop.lean::loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 288/476 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_erase: 764/1264 = 60%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_rewind: 722/1195 = 60%
   Nondeterminism.lean::a2Debit_value  reproduces  Catalog.lean::f2_loopDebit_value: 128/212 = 60%
   Primitives.lean::mapBuffer_rewind  reproduces  Primitives.lean::mapPayload_replay: 372/617 = 60%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Nondeterminism.lean::cont_core_run: 170/282 = 60%
   Primitives.lean::mapParse_first  reproduces  Primitives.lean::mapParse_block: 244/405 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::rawStrip_erase: 213/354 = 60%
   OracleSim.lean::oracleChoiceAction_apply  reproduces  OracleSim.lean::oracleChoice_initial: 145/241 = 60%
   Loop.lean::loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Catalog.lean::f2_loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   RecordTable.lean::rt_find_skip_phase  reproduces  RecordTable.lean::rt_find_scan_phase: 344/572 = 60%
   Catalog.lean::f2_loopHost_borrow  reproduces  Loop.lean::loopHost_borrow: 258/429 = 60%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 461/767 = 60%
   Loop.lean::loopHost_release  reproduces  Catalog.lean::f2_loopHost_release: 524/872 = 60%
   Catalog.lean::seekEndTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 859/1430 = 60%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::extract_rewind: 448/746 = 60%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::extract_rewind: 448/746 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Nondeterminism.lean::cont_mask_count  reproduces  Nondeterminism.lean::b2_unary_run: 81/135 = 60%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::scanCopy_run: 289/482 = 60%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::scanCopy_finish: 154/257 = 60%
   UniversalStartup.lean::universalCaptureTM  reproduces  Universal.lean::timedCaptureTM: 291/486 = 60%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitCount_over: 82/137 = 60%
   Catalog.lean::f2_splitRestore_scan  reproduces  Primitives.lean::splitCount_over: 82/137 = 60%
   Loop.lean::loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_reframe: 484/809 = 60%
   Primitives.lean::emitter_compare_scan  reproduces  Primitives.lean::emitterP2_erase_scan: 189/316 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::splitPrepare_scan: 382/639 = 60%
   Loop.lean::emCall_track_initial  reproduces  Universal.lean::timedCapture_init: 190/318 = 60%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_loopCfgTM: 95/159 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Primitives.lean::pairDupTM  reproduces  Primitives.lean::incFixedTM: 283/474 = 60%
   Primitives.lean::pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Primitives.lean::incFixedTM: 283/474 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Loop.lean::loopCall  reproduces  Loop.lean::emLoopCall: 80/134 = 60%
   Primitives.lean::splitBody_restore  reproduces  Primitives.lean::splitBody_rewind: 321/538 = 60%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::emitterAppend_run: 318/533 = 60%
   Catalog.lean::f2_extract_block  reproduces  Primitives.lean::extract_first: 170/285 = 60%
   MathlibBridge.lean::bridgeCfg_pop_emit  reproduces  MathlibBridge.lean::bridgeCfg_push_input: 195/327 = 60%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_clear_heads: 124/208 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Universal.lean::timedCut_read_fixed  reproduces  Universal.lean::timedCut_skip_fixed: 420/705 = 60%
   Primitives.lean::emitter_bits_injective  reproduces  Catalog.lean::f2_loopValue_bits: 84/141 = 60%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Catalog.lean::f2_loopValue_bits: 84/141 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipState: 215/361 = 60%
   Catalog.lean::catalog_redirect_loop  reproduces  Universal.lean::timedFrame_run: 75/126 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   CfgRecord.lean::recordStep_read_prefix  reproduces  CfgRecord.lean::recordStep_clear_snapshot: 712/1198 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeParser.lean::codeReadSymbols_sound: 142/239 = 59%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 461/776 = 59%
   Universal.lean::timedClock_step  reproduces  Universal.lean::timed_output_step: 158/266 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::extract_rewind: 443/746 = 59%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::extract_rewind: 443/746 = 59%
   Catalog.lean::f2_lenCfg  reproduces  Primitives.lean::mapCfg: 95/160 = 59%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopTM: 457/770 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamRelease_step_right: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  Seam.lean::seamComp_step_right: 80/135 = 59%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_pair: 138/233 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   CfgRecord.lean::recordStep_restore_digits  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   CfgRecord.lean::recordStep_prepare_native  reproduces  CfgRecord.lean::recordStep_clear_heads: 123/208 = 59%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::splitRestore_rewind: 467/790 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   CodeParser.lean::codeReadWrite  reproduces  CodeParser.lean::codeReadOutput: 65/110 = 59%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::splitRestore_rewind: 466/790 = 59%
   Catalog.lean::f2_counter_rewind  reproduces  Primitives.lean::emitterToken_separator: 128/217 = 59%
   Catalog.lean::f2_loopCall  reproduces  Loop.lean::emLoopCall: 79/134 = 59%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::emitterP2_erase_scan: 186/316 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::emitterP2_erase_scan: 186/316 = 59%
   Primitives.lean::catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Primitives.lean::splitEmbed_cut  reproduces  Universal.lean::timedFrame_run: 74/126 = 59%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Universal.lean::timedFrame_run: 74/126 = 59%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Universal.lean::timedFrame_run: 74/126 = 59%
   UniversalBlock.lean::universal_apply_record  reproduces  Universal.lean::timedCut_Interpreter_first: 169/288 = 59%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Interpreter_first: 169/288 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 448/764 = 59%
   Primitives.lean::splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   Primitives.lean::catalogPoly_setup  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   Primitives.lean::catalogPoly_emit  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Primitives.lean::emitterToken_separator: 127/217 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamRelease_step_right: 79/135 = 59%
   CounterLoop.lean::counter_work_step  reproduces  Seam.lean::seamComp_step_right: 79/135 = 59%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 447/764 = 59%
   Nondeterminism.lean::NP_subset_iUnion_NTIME  reproduces  Nondeterminism.lean::NEXP_subset_iUnion_NTIME: 62/106 = 58%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_fintype: 76/130 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  Universal.lean::timed_pair_separator: 121/207 = 58%
   UniversalStartup.lean::universalCanon_run  reproduces  Universal.lean::timedCanon_run: 187/320 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 448/767 = 58%
   Loop.lean::loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Catalog.lean::f2_loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::rawStrip_replay: 237/406 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::rawStrip_replay: 237/406 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Primitives.lean::extract_suffix  reproduces  Catalog.lean::f2_extract_first: 175/300 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Interpreter_first: 168/288 = 58%
   UniversalBlock.lean::universal_apply_record  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 169/290 = 58%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 169/290 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 184/316 = 58%
   Nondeterminism.lean::a2_load_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 184/316 = 58%
   Primitives.lean::pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 289/497 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Primitives.lean::lenParse_run  reproduces  Primitives.lean::extract_run: 1077/1854 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Primitives.lean::rawStrip_erase  reproduces  Universal.lean::timedCapture_transfer: 72/124 = 58%
   Catalog.lean::f2_rawStrip_erase  reproduces  Universal.lean::timedCapture_transfer: 72/124 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Loop.lean::loopHost_borrow  reproduces  Catalog.lean::f2_loopHost_borrow: 258/445 = 58%
   Primitives.lean::extract_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 448/773 = 58%
   Catalog.lean::f2_extract_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 448/773 = 58%
   Scan.lean::writeConstTM  reproduces  Scan.lean::writeAdvTM: 62/107 = 58%
   Oracle.lean::runFrom_plainEmptyOracle  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   Embed.lean::embedThroughHalt  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   Catalog.lean::a2_mapSetup_heads  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 168/290 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Loop.lean::exists_loopFindTM  reproduces  Loop.lean::exists_loopCfgTM: 92/159 = 58%
   CfgRecord.lean::recordStep_copyback_run  reproduces  CfgRecord.lean::recordStep_empty_run: 313/541 = 58%
   Loop.lean::emCall_clear_left  reproduces  Loop.lean::emCall_clear_scan: 369/638 = 58%
   Primitives.lean::rawStrip_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 447/773 = 58%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 447/773 = 58%
   Loop.lean::loopBody_run  reproduces  Nondeterminism.lean::b2_unary_run: 78/135 = 58%
   Catalog.lean::f2_loopBody_run  reproduces  Nondeterminism.lean::b2_unary_run: 78/135 = 58%
   Primitives.lean::splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 443/767 = 58%
   Catalog.lean::seekStartTM_run_ofCfg  reproduces  Catalog.lean::skipTM_run_ofCfg: 825/1430 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Primitives.lean::incFixed_computes  reproduces  Primitives.lean::emitterToken_separator: 125/217 = 58%
   Catalog.lean::f2_incFixed_computes  reproduces  Primitives.lean::emitterToken_separator: 125/217 = 58%
   Nondeterminism.lean::a2_envelope  reproduces  Nondeterminism.lean::a3n_scaled_envelope: 535/929 = 58%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 237/412 = 58%
   CodeSimulator.lean::h1Round_restore  reproduces  CodeSimulator.lean::h1Data_shift: 115/200 = 57%
   CodeSimulator.lean::h1Round_prepare  reproduces  CodeSimulator.lean::h1Data_shift: 115/200 = 57%
   Loop.lean::emCallTripleEmbedding  reproduces  Loop.lean::emCallPairEmbedding: 69/120 = 57%
   Loop.lean::emCall_track_stamp  reproduces  Loop.lean::emCall_track_initial: 398/693 = 57%
   CfgRecord.lean::recordStep_clear_snapshot  reproduces  CfgRecord.lean::recordStep_map_snapshot: 875/1525 = 57%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Catalog.lean::f2_splitRestore_rewind: 467/814 = 57%
   Nondeterminism.lean::cont_split_answer  reproduces  Nondeterminism.lean::cont_split_length: 110/192 = 57%
   UniversalInterpreter.lean::universalRecords  reproduces  CodeFormat.lean::codeTable2Bits: 134/234 = 57%
   CodeSimulator.lean::h1Round_restore  reproduces  CodeSimulator.lean::h1Round_prepare: 3055/5336 = 57%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Catalog.lean::f2_splitRestore_rewind: 466/814 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Universal.lean::timed_universal  reproduces  Universal.lean::timed_universal_concrete: 384/671 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Nondeterminism.lean::choiceCore_step  reproduces  Nondeterminism.lean::cont_write_apply: 183/320 = 57%
   CodeParser.lean::codeReadState_sound  reproduces  CodeParser.lean::codeReadUnary_sound: 223/390 = 57%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::rawStrip_replay: 232/406 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::rawStrip_replay: 232/406 = 57%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_pair_triple: 92/161 = 57%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Catalog.lean::a2_mapVirtual_run  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Loop.lean::loop_output_length_le: 145/254 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Loop.lean::emCall_track_initial  reproduces  Loop.lean::emCall_track_stamp: 398/698 = 57%
   Catalog.lean::f2_lenParse_run  reproduces  Primitives.lean::extract_run: 1057/1854 = 57%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 331/581 = 57%
   Loop.lean::emCall_finish_transfer  reproduces  Loop.lean::emCall_finish_arg: 819/1438 = 57%
   Loop.lean::emCall_track_initial  reproduces  UniversalStartup.lean::universalCapture_init: 190/334 = 57%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalInterpreter.lean::universal_unary_copy: 560/987 = 57%
   Loop.lean::emLoopCall  reproduces  Loop.lean::loopCall: 80/141 = 57%
   CfgRecord.lean::recordStep_position_run  reproduces  CfgRecord.lean::recordStep_copyback_run: 1173/2070 = 57%
   Primitives.lean::extract_block  reproduces  Catalog.lean::f2_extract_first: 170/300 = 57%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_unary_copy: 558/985 = 57%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_fuel_return: 666/1176 = 57%
   CfgRecord.lean::RecordEqIndex  reproduces  CfgRecord.lean::RecordTestIndex: 73/129 = 57%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 427/755 = 57%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_skip_unary: 709/1254 = 57%
   OracleSim.lean::oracleMarkedCfg  reproduces  OracleSim.lean::oracleBackCfg: 91/161 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   MathlibBridge.lean::bridge_back  reproduces  MathlibBridge.lean::bridge_scan: 422/747 = 56%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Loop.lean::emCallPairIndex  reproduces  Loop.lean::emCallPairSelect: 61/108 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   Nondeterminism.lean::b2_unary_run  reproduces  Catalog.lean::a2_mapSetup_run: 92/163 = 56%
   UHaltMachine.lean::bits_foldr_bit_one  reproduces  UHaltMachine.lean::foldr_bit_one_pos: 62/110 = 56%
   UniversalInterpreter.lean::universal_state_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedPrefix_clock_end  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedPrefix_clock  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedCut_state_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Nondeterminism.lean::a2_load_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   MathlibBridge.lean::bridge_seed  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   MathlibBridge.lean::bridge_back  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Loop.lean::emCall_track_run  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Primitives.lean::emitterP2_prepare_candidate  reproduces  Primitives.lean::emitterP2_erase_scan: 178/316 = 56%
   Loop.lean::loop_rewind_bounded  reproduces  Primitives.lean::catalogRewind: 245/435 = 56%
   Loop.lean::loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Primitives.lean::catalogRewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalBlock.lean::universal_skip_unary: 673/1196 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Universal.lean::timedCanon_start  reproduces  UniversalStartup.lean::universalCanon_start: 189/336 = 56%
   Primitives.lean::rawStrip_erase  reproduces  UniversalStartup.lean::universalCapture_transfer: 72/128 = 56%
   Catalog.lean::f2_rawStrip_erase  reproduces  UniversalStartup.lean::universalCapture_transfer: 72/128 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::emitterToken_separator: 122/217 = 56%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Primitives.lean::emitterToken_separator: 122/217 = 56%
   Primitives.lean::splitBodyStateDecidableEq  reproduces  Primitives.lean::emitterP2StateDecidableEq: 408/726 = 56%
   Catalog.lean::f2_splitBodyStateDecidableEq  reproduces  Primitives.lean::emitterP2StateDecidableEq: 408/726 = 56%
   CodeSimulator.lean::canonHeader_length  reproduces  CodeSimulator.lean::canonHeaderOK_iff: 82/146 = 56%
   Nondeterminism.lean::e3_shift_scan  reproduces  Catalog.lean::f2_idTM_run: 434/773 = 56%
   Loop.lean::emCall_finish_arg  reproduces  Loop.lean::emCall_finish_transfer: 819/1459 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Primitives.lean::extract_rewind  reproduces  Primitives.lean::splitRestore_rewind: 443/790 = 56%
   Catalog.lean::f2_extract_rewind  reproduces  Primitives.lean::splitRestore_rewind: 443/790 = 56%
   RecordTable.lean::joinFields_cfgRecord_length  reproduces  RecordTable.lean::cfgRecord_init: 111/198 = 56%
   UniversalInterpreter.lean::universalRecords  reproduces  CodeSimulator.lean::tableBitsK: 79/141 = 56%
   Codes2Tape.lean::Code2TM.serialize  reproduces  CodeSimulator.lean::tableBitsK: 79/141 = 56%
   Embed.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Primitives.lean::computesFunInTime_prepend  reproduces  Catalog.lean::computesFunInTime_prepend_spaceUsed: 122/218 = 56%
   Primitives.lean::rawStrip_rewind  reproduces  Primitives.lean::splitRestore_rewind: 442/790 = 56%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Primitives.lean::splitRestore_rewind: 442/790 = 56%
   Catalog.lean::catalogCopyF  reproduces  Scan.lean::scanWriteCfg: 113/202 = 56%
   Primitives.lean::mapCfg  reproduces  Primitives.lean::lenCfg: 99/177 = 56%
   Loop.lean::emCall_exit_fixed  reproduces  OracleSim.lean::oracleBankCfg_eq: 203/363 = 56%
   Nondeterminism.lean::a3n_eq_parse  reproduces  Nondeterminism.lean::cont_parse_run: 350/626 = 56%
   Catalog.lean::f2_lenParse_block  reproduces  Primitives.lean::lenParse_first: 172/308 = 56%
   Catalog.lean::a2_map_parse  reproduces  Primitives.lean::extract_run: 1035/1854 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   OracleSim.lean::oracleChoice_initial  reproduces  OracleSim.lean::oracleChoiceAction_apply: 145/260 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timedClockPrefix_length: 78/140 = 56%
   Primitives.lean::emitterToken_double  reproduces  Primitives.lean::scanStep_right: 88/158 = 56%
   Primitives.lean::extract_replay_finish  reproduces  Universal.lean::timedCapture_transfer: 69/124 = 56%
   Catalog.lean::f2_extract_replay_finish  reproduces  Universal.lean::timedCapture_transfer: 69/124 = 56%
   UniversalStartup.lean::universalPrefix_start  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   UniversalStartup.lean::universalPrefix_bits  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedPrefix_complete  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedPrefix_code  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Seam.lean::seamRelease_run_pos  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::splitEmit_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::pairDup_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::pairDup_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::incFixed_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::emitterP2_prepare_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Oracle.lean::runFrom_ofMultiTapeTM  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   MathlibBridge.lean::bridge_emit  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_pairDup_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_pairDup_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_incFixed_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::pairDup_double: 653/1176 = 56%
   Catalog.lean::f2_idTM_run  reproduces  Nondeterminism.lean::e3_shift_scan: 434/782 = 55%
   Loop.lean::emCall_bank_final  reproduces  Loop.lean::emCall_finish_initial: 904/1629 = 55%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Loop.lean::loopHost_halt_return: 389/701 = 55%
   CodeSimulator.lean::h1Round_effect  reproduces  CodeSimulator.lean::h1Data_stateCell: 71/128 = 55%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::pairDup_double: 652/1176 = 55%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 322/581 = 55%
   Primitives.lean::emitterP2_erase_scan  reproduces  Primitives.lean::rawStrip_replay: 225/406 = 55%
   Primitives.lean::lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1057/1908 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_erase_scan: 175/316 = 55%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_skip_unary: 694/1254 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 479/866 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 479/866 = 55%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::scanCopy_finish: 142/257 = 55%
   CodeSimulator.lean::h1ReadActions_at  reproduces  CodeSimulator.lean::h1Table_groups: 79/143 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 477/866 = 55%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 477/866 = 55%
   RecordTable.lean::rt_copyState  reproduces  RecordTable.lean::rt_copyState_decidableEq: 76/138 = 55%
   Primitives.lean::emitter_compare_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 427/776 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Primitives.lean::incFixedTM  reproduces  Primitives.lean::emitterTokenTM: 220/400 = 55%
   Catalog.lean::f2_incFixedTM  reproduces  Primitives.lean::emitterTokenTM: 220/400 = 55%
   UniversalStartup.lean::universal_pair_length  reproduces  Universal.lean::timedClockPrefix_length: 77/140 = 55%
   Primitives.lean::splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 476/866 = 55%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 476/866 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   CfgRecord.lean::RecordTestIndex  reproduces  CfgRecord.lean::RecordEqIndex: 73/133 = 55%
   Loop.lean::emLoopCall  reproduces  Catalog.lean::f2_loopCall: 79/144 = 55%
   Scan.lean::scanWriteCfg  reproduces  Catalog.lean::catalogCopyF: 113/206 = 55%
   Primitives.lean::splitEmbed_cut  reproduces  Primitives.lean::emitter_first_entry: 221/403 = 55%
   Primitives.lean::splitEmbed_cut  reproduces  Loop.lean::emCall_first_entry: 221/403 = 55%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Primitives.lean::emitter_first_entry: 221/403 = 55%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Loop.lean::emCall_first_entry: 221/403 = 55%
   Primitives.lean::rawStrip_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Primitives.lean::rawStrip_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Primitives.lean::extract_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Primitives.lean::extract_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_rawStrip_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   UniversalStartup.lean::universalCanon_start  reproduces  Universal.lean::timedCanon_start: 189/345 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Nondeterminism.lean::b2_unary_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   UniversalBlock.lean::universal_skip_groups  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   UniversalBlock.lean::universal_prepare_next  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   UniversalBlock.lean::universal_live_block  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Universal.lean::timedCut_skip_groups  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Nondeterminism.lean::cont_rewind_input  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Primitives.lean::emitter_compare_run  reproduces  Primitives.lean::emitterP2_erase_scan: 173/316 = 55%
   Loop.lean::loopHost_body_run  reproduces  Catalog.lean::f2_loopHost_body_capture: 64/117 = 55%
   Loop.lean::loopBodyCfg  reproduces  Oracle.lean::Cfg.embedOracle: 100/183 = 55%
   Catalog.lean::f2_loopBodyCfg  reproduces  Oracle.lean::Cfg.embedOracle: 100/183 = 55%
   Primitives.lean::emitterP2_erase_scan  reproduces  Catalog.lean::f2_rawStrip_replay: 225/412 = 55%
   Loop.lean::loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 203/372 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Primitives.lean::extract_run  reproduces  Primitives.lean::pairValid_run: 641/1177 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  UniversalStartup.lean::universalCapture_run: 92/169 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Universal.lean::timedCapture_run: 92/169 = 54%
   Nondeterminism.lean::b2_unary_run  reproduces  UniversalStartup.lean::universalCapture_run: 92/169 = 54%
   Nondeterminism.lean::b2_unary_run  reproduces  Universal.lean::timedCapture_run: 92/169 = 54%
   UniversalBlock.lean::universal_prepare_next  reproduces  UniversalBlock.lean::universal_skip_unary: 651/1196 = 54%
   Primitives.lean::catalogPayload_length  reproduces  Catalog.lean::f2_first_length: 86/158 = 54%
   Primitives.lean::extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 443/814 = 54%
   Primitives.lean::extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Nondeterminism.lean::NEXP_subset_iUnion_NTIME  reproduces  Nondeterminism.lean::NP_subset_iUnion_NTIME: 62/114 = 54%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_clock_get: 205/377 = 54%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Primitives.lean::catalogPoly_emit: 275/506 = 54%
   Catalog.lean::f2_timed_control_init  reproduces  Nondeterminism.lean::cont_guess_initial: 113/208 = 54%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_skip_fixed: 383/705 = 54%
   Primitives.lean::rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_ready_done: 393/724 = 54%
   Catalog.lean::a2_map_block  reproduces  Primitives.lean::extract_block: 355/654 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::f2_timed_branch_run  reproduces  Nondeterminism.lean::cont_core_run: 153/282 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Catalog.lean::f2_loopBorrow_run  reproduces  Loop.lean::loopHost_borrow_run: 288/531 = 54%
   MathlibBridge.lean::codePrimSkipTable2  reproduces  MathlibBridge.lean::codePrimSkipTable1: 135/249 = 54%
   Primitives.lean::splitEmit_suffix  reproduces  Loop.lean::loopReplay_run: 187/345 = 54%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Loop.lean::loopReplay_run: 187/345 = 54%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 469/866 = 54%
   Primitives.lean::pairValid_computes  reproduces  Primitives.lean::anyTrue_computes: 137/253 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_extract_run  reproduces  Primitives.lean::pairValid_run: 637/1177 = 54%
   Primitives.lean::splitBody_prepare  reproduces  Primitives.lean::splitBody_restore: 270/499 = 54%
   Loop.lean::loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 285/527 = 54%
   Primitives.lean::catalogPoly_unary_computes  reproduces  Primitives.lean::splitPoly_loop_end: 380/703 = 54%
   Primitives.lean::emitterP2_prepare_run  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 468/866 = 54%
   Nondeterminism.lean::a2Value_bits  reproduces  CodeParser.lean::codeBitsNat_bits: 87/161 = 54%
   Loop.lean::loopValue_bits  reproduces  CodeParser.lean::codeBitsNat_bits: 87/161 = 54%
   Catalog.lean::f2_loopValue_bits  reproduces  CodeParser.lean::codeBitsNat_bits: 87/161 = 54%
   Catalog.lean::f2_counterInc_bits  reproduces  CodeParser.lean::codeBitsNat_bits: 87/161 = 54%
   Nondeterminism.lean::cont_mask_count  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 81/150 = 54%
   Primitives.lean::splitEmit_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Primitives.lean::scanCopy_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Primitives.lean::extract_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Primitives.lean::emitterToken_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Primitives.lean::catalogPoly_loop  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Nondeterminism.lean::a3n_eq_double  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Nondeterminism.lean::a2Borrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   MathlibBridge.lean::bridge_statement  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::loopHost_borrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::emCall_finish_transfer  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::emCall_finish_rewind  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::emCall_finish_erase  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::emCall_finish_arg  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_loopBorrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_extract_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_counter_carry  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_catalogPoly_loop  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_backB  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_backA  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Loop.lean::exists_emitLoopTM  reproduces  Loop.lean::exists_loopFindTM: 491/910 = 54%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 467/866 = 54%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_candidate: 467/866 = 54%
   Primitives.lean::extract_replay_finish  reproduces  UniversalStartup.lean::universalCapture_transfer: 69/128 = 54%
   Loop.lean::emCallPairEmbedding  reproduces  Loop.lean::emCallTripleEmbedding: 69/128 = 54%
   Catalog.lean::f2_extract_replay_finish  reproduces  UniversalStartup.lean::universalCapture_transfer: 69/128 = 54%
   Loop.lean::emCall_track_run  reproduces  Loop.lean::emCall_track_extent: 145/269 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   UniversalBlock.lean::universal_read_fixed  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 358/665 = 54%
   Primitives.lean::splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 466/866 = 54%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Primitives.lean::emitterP2_prepare_rewind_suffix: 466/866 = 54%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 652/1212 = 54%
   Primitives.lean::lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 172/320 = 54%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_clear_trace: 869/1617 = 54%
   Primitives.lean::splitEmit_double  reproduces  Primitives.lean::splitEmit_separator: 411/765 = 54%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Primitives.lean::splitPrepare_extra: 242/451 = 54%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Loop.lean::loopHost_borrow_rewind: 633/1181 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timed_replay  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Loop.lean::emCall_right_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_guess_return: 316/590 = 54%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedCut_skip_unary: 671/1254 = 54%
   Nondeterminism.lean::e3_find_eq  reproduces  Primitives.lean::splitFind_eq: 122/228 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Loop.lean::emCall_right_run: 92/172 = 53%
   Nondeterminism.lean::b2_unary_run  reproduces  Loop.lean::emCall_right_run: 92/172 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Primitives.lean::pairDup_computes  reproduces  Primitives.lean::emitterToken_separator: 116/217 = 53%
   Catalog.lean::f2_pairDup_computes  reproduces  Primitives.lean::emitterToken_separator: 116/217 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Universal.lean::timedCut_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 518/970 = 53%
   Loop.lean::emCall_track_action  reproduces  Loop.lean::emCall_track_initial: 370/693 = 53%
   Nondeterminism.lean::e3_split_of_body  reproduces  Catalog.lean::f2_splitSolve_of_body: 717/1343 = 53%
   Seam.lean::seamRelease_run_pos  reproduces  Nondeterminism.lean::b2_unary_run: 72/135 = 53%
   Loop.lean::emCall_bank_initial  reproduces  Loop.lean::emCall_prepare_final: 377/707 = 53%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Loop.lean::exists_emitLoopTM: 1204/2258 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitter_compare_rewind: 479/899 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitter_compare_rewind: 479/899 = 53%
   Primitives.lean::splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Universal.lean::timedCapture_transfer: 66/124 = 53%
   Nondeterminism.lean::a2_load_rewind  reproduces  Universal.lean::timedCapture_transfer: 66/124 = 53%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Universal.lean::timedCapture_transfer: 66/124 = 53%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Universal.lean::timedCapture_transfer: 66/124 = 53%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_guess_return: 314/590 = 53%
   Nondeterminism.lean::e3_loop_bound  reproduces  Primitives.lean::emitterSplit_loop_bound: 91/171 = 53%
   Catalog.lean::f2_splitEmit_double  reproduces  Primitives.lean::splitPrepare_scan: 340/639 = 53%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalBlock.lean::universal_skip_unary: 636/1196 = 53%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_table_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_skip_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalBlock.lean::universal_skip_unary  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalBlock.lean::universal_read_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_output_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_clock_success  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_clock_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_table_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_skip_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_read_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::splitRestore_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::splitPrepare_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::rawStrip_trim  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::rawStrip_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::mapBuffer_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::extract_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitter_compare_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitterToken_separator  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitterToken_double  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::emitterP2_erase_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::catalogPoly_setup  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::catalogPoly_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::catalogPoly_emit  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Primitives.lean::anyTrue_run  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Loop.lean::loopHost_reject  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Loop.lean::emCall_right_scan  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_rawStrip_trim  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_reject  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_counter_increment  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Loop.lean::emCall_clear_left  reproduces  Primitives.lean::emitterP2_erase_scan: 168/316 = 53%
   Primitives.lean::rawStrip_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Primitives.lean::rawStrip_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Primitives.lean::extract_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Primitives.lean::extract_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_rawStrip_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Primitives.lean::emitterP2_erase_back  reproduces  Primitives.lean::emitterToken_separator: 115/217 = 53%
   Oracle.lean::runFrom_ofMultiTapeTM  reproduces  Oracle.lean::runFrom_plainEmptyOracle: 115/217 = 53%
   Catalog.lean::catalog_copy_trace  reproduces  Catalog.lean::catalog_copy_forward: 259/489 = 53%
   Loop.lean::emCall_triple_pair  reproduces  Loop.lean::emCall_triple_other: 152/287 = 53%
   Primitives.lean::splitPrepare_extra  reproduces  Primitives.lean::splitPrepare_scan: 338/639 = 53%
   Nondeterminism.lean::a2Borrow_step  reproduces  Loop.lean::loopReplay_step: 174/329 = 53%
   Catalog.lean::f2_loopBorrow_step  reproduces  Loop.lean::loopReplay_step: 174/329 = 53%
   Universal.lean::timedCut_prepare_next  reproduces  UniversalInterpreter.lean::universal_initial_skip: 513/970 = 53%
   CodeSimulator.lean::h1Seek_groups  reproduces  CodeSimulator.lean::h1Seek_lookup: 1057/2000 = 53%
   Loop.lean::emCall_track_stamp  reproduces  Universal.lean::timedCapture_init: 168/318 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Primitives.lean::catalogFirstEntry: 198/375 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Primitives.lean::mapCfg  reproduces  Catalog.lean::f2_lenCfg: 95/180 = 53%
   Primitives.lean::mapValidate  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Primitives.lean::lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Primitives.lean::anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_lenSuffix_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 79/150 = 53%
   OracleSim.lean::oracleShadowAction  reproduces  OracleSim.lean::oracleChoiceAction: 60/114 = 53%
   Universal.lean::timed_clock_success  reproduces  Universal.lean::timed_clock_timeout: 513/975 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   UniversalInterpreter.lean::universal_state_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Universal.lean::timedCut_state_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   CodeFormat.lean::actionBitsK  reproduces  CodeFormat.lean::actionBits₂: 93/177 = 53%
   Primitives.lean::pairDup_computes  reproduces  Primitives.lean::scanStep_right: 83/158 = 53%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::scanCopy_finish: 135/257 = 53%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeFormat.lean::codeReadWork_sound: 127/242 = 52%
   Catalog.lean::clearTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 329/627 = 52%
   Catalog.lean::catalog_clear_trace  reproduces  Catalog.lean::catalog_transfer_trace: 869/1657 = 52%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Primitives.lean::mapValidate  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Loop.lean::loopReplay_run  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Catalog.lean::f2_loopReplay_run  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Catalog.lean::f2_counter_rewind  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Loop.lean::emCall_finish_erase  reproduces  Loop.lean::emCall_finish_transfer: 764/1459 = 52%
   Loop.lean::emCall_triple_inverse  reproduces  Loop.lean::emCall_triple_pair: 122/233 = 52%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Primitives.lean::extract_replay_finish: 156/298 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::extract_replay_finish: 156/298 = 52%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_skip_fixed: 369/705 = 52%
   Nondeterminism.lean::e3_find_eq  reproduces  Primitives.lean::emitterSplit_find: 123/235 = 52%
   CodeParser.lean::codeEraseVec  reproduces  CodeFormat.lean::codeEraseWork: 113/216 = 52%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Primitives.lean::rawStrip_rewind: 368/704 = 52%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Primitives.lean::rawStrip_rewind: 368/704 = 52%
   OracleSim.lean::oracleBack_run  reproduces  OracleSim.lean::oracleMarker_step: 199/381 = 52%
   OracleNondeterministic.lean::AcceptsWithin  reproduces  Nondeterminism.lean::choiceVerifier: 71/136 = 52%
   Catalog.lean::a2_map_setup  reproduces  Loop.lean::loopFuel_init: 214/410 = 52%
   Primitives.lean::catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 275/527 = 52%
   Loop.lean::loopHost_borrow_rewind  reproduces  Loop.lean::loopHost_payload_scan: 359/688 = 52%
   Primitives.lean::emitter_bits_injective  reproduces  CodeParser.lean::codeBitsNat_bits: 84/161 = 52%
   Nondeterminism.lean::e3c_bits_injective  reproduces  CodeParser.lean::codeBitsNat_bits: 84/161 = 52%
   OracleSim.lean::oracleHost_initial  reproduces  OracleSim.lean::oraclePrepare_tail: 72/138 = 52%
   Universal.lean::timed_input_layout  reproduces  Universal.lean::timedClockPrefix_length: 73/140 = 52%
   Primitives.lean::splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Primitives.lean::catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Primitives.lean::catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Oracle.lean::runFrom_plainEmptyOracle  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   CodeFormat.lean::codeReadActionK_sound  reproduces  CodeFormat.lean::codeReadWork_sound: 126/242 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Loop.lean::loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Loop.lean::loopControl_payload: 128/246 = 52%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Primitives.lean::extract_replay_finish: 155/298 = 52%
   Nondeterminism.lean::a2_load_rewind  reproduces  Primitives.lean::extract_replay_finish: 155/298 = 52%
   Primitives.lean::catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Loop.lean::loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_loopBody_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_counter_carry  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_catalogPoly_loop  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 78/150 = 52%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Primitives.lean::splitRestore_scan: 432/831 = 52%
   Primitives.lean::pairValid_run  reproduces  Primitives.lean::anyTrue_run: 413/795 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Primitives.lean::rawStrip_copy  reproduces  Primitives.lean::emitterP2_erase_scan: 164/316 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Primitives.lean::emitterP2_erase_scan: 164/316 = 52%
   Scan.lean::scan_const_trace  reproduces  Scan.lean::scan_adv_run: 247/476 = 52%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::a2Borrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Loop.lean::loopHost_borrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Catalog.lean::f2_loopBorrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Primitives.lean::emitterP2_erase_back  reproduces  Catalog.lean::f2_rawStrip_erase: 188/363 = 52%
   Loop.lean::emCall_finish_initial  reproduces  Loop.lean::emCall_prepare_final: 366/707 = 52%
   Primitives.lean::extract_run  reproduces  Catalog.lean::f2_pairValid_run: 637/1231 = 52%
   Nondeterminism.lean::b2_verify_step  reproduces  Nondeterminism.lean::b2_ready_step: 327/632 = 52%
   CodeSimulator.lean::h1Succ_trace  reproduces  CodeSimulator.lean::h1Succ_run: 124/240 = 52%
   UniversalInterpreter.lean::universalRecords  reproduces  Codes2Tape.lean::Code2TM.serialize: 160/310 = 52%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Primitives.lean::computesFunInTime_pairFst: 80/155 = 52%
   Primitives.lean::splitEmit_separator  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Primitives.lean::lenSuffix_run  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Nondeterminism.lean::b2_verify_run  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Nondeterminism.lean::b2_guess_run  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Loop.lean::loopHost_fuel_copy  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_splitEmit_separator  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_lenSuffix_run  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   UniversalBlock.lean::universal_skip_unary  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 343/665 = 52%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Nondeterminism.lean::a2_load_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   CfgRecord.lean::recordStep_restore_native  reproduces  CfgRecord.lean::recordStep_reject_run: 282/547 = 52%
   OracleSim.lean::oracleLocalCfg  reproduces  OracleSim.lean::oracleBackCfg: 83/161 = 52%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Loop.lean::loopHost_fuel_return: 606/1176 = 52%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Loop.lean::loopHost_fuel_return: 606/1176 = 52%
   Nondeterminism.lean::e3_find_eq  reproduces  Catalog.lean::f2_splitFind_eq: 122/237 = 51%
   OracleNondeterministic.lean::AcceptsWithin  reproduces  Nondeterminism.lean::e3ChoiceVerifier: 71/138 = 51%
   Primitives.lean::emitterToken_run  reproduces  Primitives.lean::scanCopy_suffix: 437/850 = 51%
   Nondeterminism.lean::b2_copy_step  reproduces  Nondeterminism.lean::b2_rewind_step: 201/391 = 51%
   Loop.lean::loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Primitives.lean::lenParse_run  reproduces  Primitives.lean::pairValid_run: 605/1177 = 51%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Nondeterminism.lean::a2Borrow_correct: 166/323 = 51%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Primitives.lean::splitPrepare_rewind: 388/755 = 51%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedCut_initial_skip: 518/1008 = 51%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 322/627 = 51%
   Catalog.lean::catalog_transfer_trace  reproduces  Catalog.lean::catalog_copy_forward: 251/489 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Primitives.lean::splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 242/472 = 51%
   Primitives.lean::mapPayload_replay  reproduces  Primitives.lean::rawStrip_replay: 208/406 = 51%
   Nondeterminism.lean::a2Borrow_run  reproduces  Loop.lean::loopHost_borrow_run: 272/531 = 51%
   Primitives.lean::splitEmit_separator  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   Primitives.lean::pairDup_double  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   Catalog.lean::f2_splitEmit_separator  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   Catalog.lean::f2_pairDup_double  reproduces  Primitives.lean::emitterToken_separator: 111/217 = 51%
   UniversalInterpreter.lean::universal_table_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Universal.lean::timed_output_back  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Universal.lean::timed_clock_back  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Universal.lean::timedCut_table_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::splitEmit_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::scanCopy_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::extract_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Primitives.lean::catalogPoly_loop  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a3n_eq_double  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Loop.lean::emCall_finish_transfer  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Loop.lean::emCall_finish_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Loop.lean::emCall_finish_erase  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Loop.lean::emCall_finish_arg  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_extract_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_counter_increment  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::f2_catalogPoly_loop  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::a2_map_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::a2_map_backB  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Catalog.lean::a2_map_backA  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Universal.lean::timedCut_unary_copy  reproduces  UniversalBlock.lean::universal_skip_unary: 611/1196 = 51%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::emitter_compare_scan: 334/654 = 51%
   Primitives.lean::emitterP2_update_right  reproduces  Primitives.lean::emitterP2_words_clean: 72/141 = 51%
   Primitives.lean::emitterP2_update_left  reproduces  Primitives.lean::emitterP2_words_clean: 72/141 = 51%
   Catalog.lean::f2_lenParse_run  reproduces  Primitives.lean::pairValid_run: 601/1177 = 51%
   Primitives.lean::splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 340/666 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Nondeterminism.lean::a2Borrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 174/341 = 51%
   Universal.lean::timedClockPrefix_length  reproduces  UniversalStartup.lean::universal_pair_length: 77/151 = 51%
   UniversalBlock.lean::universal_prepare_next  reproduces  Universal.lean::timedCut_initial_skip: 513/1008 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   CodeParser.lean::codeEraseVec  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeFormat.lean::codeEraseWork  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeFormat.lean::codeEraseActionK  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 156/307 = 51%
   Loop.lean::loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Loop.lean::loopControl_payload: 125/246 = 51%
   CfgRecord.lean::recordStep_read_fields  reproduces  CfgRecord.lean::recordStep_write_back: 1389/2734 = 51%
   CodeParser.lean::codeReadUnary_sound  reproduces  CodeParser.lean::codeReadState_sound: 223/439 = 51%
   Primitives.lean::splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Catalog.lean::f2_rawStrip_rewind: 368/725 = 51%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Catalog.lean::f2_rawStrip_rewind: 368/725 = 51%
   OracleSim.lean::oracleHost_initial  reproduces  OracleSim.lean::oraclePrepare_zero: 71/140 = 51%
   MathlibBridge.lean::bridge_scan  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Primitives.lean::catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_emit: 180/355 = 51%
   Catalog.lean::f2_catalogPrefixTM_copy  reproduces  Primitives.lean::catalogPrefixTM_emit: 180/355 = 51%
   Primitives.lean::emitter_compare_rewind  reproduces  Primitives.lean::splitRestore_rewind: 400/790 = 51%
   Primitives.lean::splitRestore_scan  reproduces  Primitives.lean::splitPrepare_extra: 228/451 = 51%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 322/637 = 51%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 322/637 = 51%
   Catalog.lean::f2_splitBody_rewind  reproduces  Primitives.lean::splitBody_restore: 252/499 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Primitives.lean::scanCopy_run  reproduces  Primitives.lean::rawStrip_replay: 205/406 = 50%
   Catalog.lean::f2_scanCopy_run  reproduces  Primitives.lean::rawStrip_replay: 205/406 = 50%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 155/307 = 50%
   Nondeterminism.lean::a2_load_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 155/307 = 50%
   Primitives.lean::mapPayload_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 208/412 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Primitives.lean::scanCopy_suffix  reproduces  Primitives.lean::emitterToken_double: 396/785 = 50%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalStartup.lean::universalPrefix_start  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalStartup.lean::universalPrefix_bits  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalInterpreter.lean::universal_skip_fixed  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalInterpreter.lean::universal_count_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalBlock.lean::universal_skip_unary  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalBlock.lean::universal_skip_groups  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalBlock.lean::universal_read_fixed  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   UniversalBlock.lean::universal_prepare_next  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedPrefix_complete  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedPrefix_code  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedPrefix_clock_end  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedPrefix_clock  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_unary_copy  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_skip_unary  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_skip_groups  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_skip_fixed  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_read_fixed  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_prepare_next  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_initial_skip  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_count_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::splitRestore_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::splitPrepare_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::splitEmbed_cut  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::rawStrip_trim  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::rawStrip_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::mapBuffer_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::extract_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitter_compare_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_prepare_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_prepare_rewind_suffix  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_prepare_rewind_candidate  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::emitterP2_erase_back  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::catalogPoly_setup  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::catalogPoly_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::catalogPoly_emit  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Primitives.lean::anyTrue_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   MathlibBridge.lean::bridge_seed  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   MathlibBridge.lean::bridge_emit  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   MathlibBridge.lean::bridge_back  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Loop.lean::emCall_track_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Loop.lean::emCall_right_scan  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_rawStrip_trim  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_extract_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_counter_carry  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::f2_anyTrue_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Catalog.lean::a2_mapVirtual_run  reproduces  Nondeterminism.lean::b2_unary_run: 68/135 = 50%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_skip_fixed: 355/705 = 50%
   Loop.lean::emCall_clear_run  reproduces  Loop.lean::emCall_clear_origin: 428/850 = 50%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_start_core: 432/858 = 50%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_start_core: 432/858 = 50%
   Loop.lean::emCall_track_computes  reproduces  Loop.lean::emCall_right_computes: 77/153 = 50%
   Loop.lean::emCall_right_computes  reproduces  Loop.lean::emCall_track_computes: 77/153 = 50%
   CodeSimulator.lean::h1Skip_path  reproduces  CodeSimulator.lean::h1Skip_run: 547/1087 = 50%
   Loop.lean::emCall_track_stamp  reproduces  UniversalStartup.lean::universalCapture_init: 168/334 = 50%
   Catalog.lean::a2_mapVirtual  reproduces  VirtualInput.lean::vhostCfg: 91/181 = 50%
   Loop.lean::emCall_pair_triple  reproduces  Loop.lean::emCall_triple_inverse: 92/183 = 50%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedPrefix_live: 96/191 = 50%
   Universal.lean::timedCapture_start  reproduces  Universal.lean::timedPrefix_live: 96/191 = 50%
   Catalog.lean::compareTM_run_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Primitives.lean::emitterAppend_run  reproduces  Primitives.lean::rawStrip_replay: 204/406 = 50%
   UniversalBlock.lean::universalActions  reproduces  UniversalInterpreter.lean::universalRecords: 105/209 = 50%
   Universal.lean::timedCut_Actions  reproduces  UniversalInterpreter.lean::universalRecords: 105/209 = 50%
   Loop.lean::loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   Primitives.lean::emitterAppend_run  reproduces  Catalog.lean::f2_scanCopy_finish: 135/269 = 50%
   Primitives.lean::splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 432/861 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_map_suffix  reproduces  Primitives.lean::scanCopy_suffix: 426/850 = 50%
   Loop.lean::loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 666/1329 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Nondeterminism.lean::a2Borrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 272/544 = 50%
   Primitives.lean::pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   Primitives.lean::extract_replay_finish  reproduces  Primitives.lean::rawStrip_replay: 203/406 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Primitives.lean::rawStrip_replay: 203/406 = 50%
   Oracle.lean::runFrom_ofMultiTapeTM  reproduces  Catalog.lean::catalog_redirect_loop: 70/140 = 50%
   Nondeterminism.lean::e3_loop_result  reproduces  Nondeterminism.lean::e3_split_length: 70/140 = 50%
   Universal.lean::timedClockCfg  reproduces  Universal.lean::timed_laneCfg: 60/120 = 50%
```

## Axiom prints and recursive admission walks

Verbatim production-module evidence:

```text
'Turing.MachineFormat.exists_polyCanonizer' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Turing.MachineFormat.exists_polyCanonizer: direct sorryAx users in closure: [Turing.MachineFormat.exists_polyCanonizer]
'Turing.MachineFormat.exists_uniformSimulator' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Turing.MachineFormat.exists_uniformSimulator: direct sorryAx users in closure: [Turing.MachineFormat.exists_uniformSimulator]
'Turing.exists_uniformMachineCode2' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Turing.exists_uniformMachineCode2: direct sorryAx users in closure: [Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
'Turing.exists_uniformMachineCode' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Turing.exists_uniformMachineCode: direct sorryAx users in closure: [Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
'Complexity.EXP_subset_POracle_EXPCOM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Complexity.EXP_subset_POracle_EXPCOM: direct sorryAx users in closure: [Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
'Complexity.POracle_EXPCOM_eq_EXP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Complexity.POracle_EXPCOM_eq_EXP: direct sorryAx users in closure: [Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
'Complexity.NPOracle_EXPCOM_eq_EXP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Complexity.NPOracle_EXPCOM_eq_EXP: direct sorryAx users in closure: [Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
'Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM: direct sorryAx users in closure: [Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
'Complexity.NPOracle_EXPCOM_subset_EXP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Complexity.NPOracle_EXPCOM_subset_EXP: direct sorryAx users in closure: [Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
'Complexity.baker_gill_solovay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Complexity.baker_gill_solovay: direct sorryAx users in closure: [Turing.MachineFormat.exists_polyCanonizer,
 Turing.MachineFormat.exists_uniformSimulator]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1WorkReads_mem: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1WorkReads_mem: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1WorkReads_length: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1WorkReads_length: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1WorkRank: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1WorkRank: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1InputRank: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1InputRank: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1ReadRank: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1ReadRank: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SuccPhase: axioms: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SuccPhase: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SuccTM: axioms: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SuccTM: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1UnaryCfg: axioms: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1UnaryCfg: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Unary_step: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Unary_step: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Unary_run: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Unary_run: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1AfterTag: axioms: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1AfterTag: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Succ_trace: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Succ_trace: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Succ_run: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Succ_run: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Succ_cut: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Succ_cut: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Succ_heads: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Succ_heads: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipPh: axioms: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipPh: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipPart: axioms: [propext, Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipPart: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipRed: axioms: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipRed: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipTM: axioms: [propext, Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipTM: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Skip_fixed: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Skip_fixed: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Skip_tail: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Skip_tail: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Action_split: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Action_split: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Reads_append: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Reads_append: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Action_reads: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Action_reads: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Skip_run: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Skip_run: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Skip_path: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Skip_path: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Skip_spec: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Skip_spec: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipPh_finite: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipPh_finite: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipPh_decidable: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SkipPh_decidable: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekCtrl: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekCtrl: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekRouter: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekRouter: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekNext: axioms: [propext, Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekNext: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekKey: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekKey: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekPh: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekPh: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekPart: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekPart: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekRed: axioms: [propext, Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekRed: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekTM: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekTM: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekCfg: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekCfg: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_request: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_request: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekCost: axioms: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekCost: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_many: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_many: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_stateStep: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_stateStep: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_rank: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_rank: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekShift: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekShift: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_groups: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_groups: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_observe: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_observe: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1ReadActions: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1ReadActions: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1ReadActions_length: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1ReadActions_length: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1ReadActions_at: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1ReadActions_at: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Table_groups: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Table_groups: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Table_cut: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Table_cut: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Records_length: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Records_length: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Run_headBound: axioms: [propext,
 Classical.choice,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Run_headBound: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Run_input: axioms: [propext, Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Run_input: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Groups_length: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Groups_length: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_lookup: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_lookup: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Unary_read: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Unary_read: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SummaryState: axioms: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SummaryState: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SummaryState_cell: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SummaryState_cell: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SummaryState_update: axioms: [Quot.sound,
 propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SummaryState_update: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Buffer_outside: axioms: [propext,
 Classical.choice,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Buffer_outside: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SummaryState_copy: axioms: [Quot.sound,
 propext,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SummaryState_copy: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SummaryState_clear: axioms: [Quot.sound,
 propext,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SummaryState_clear: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_select: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Seek_select: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1TwoMoveTM: axioms: [propext, Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1TwoMoveTM: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1TwoMove_run: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1TwoMove_run: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekPh_finite: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekPh_finite: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekPh_decidable: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1SeekPh_decidable: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundKey: axioms: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundKey: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundPh: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundPh: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundPart: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundPart: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundExit: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundExit: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundRed: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundRed: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundTM: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundTM: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundPh_finite: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundPh_finite: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundPh_decidable: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundPh_decidable: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundFinTM: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundFinTM: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Data: axioms: [propext, Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Data: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Mirror_ne_summary: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Mirror_ne_summary: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Data_shift: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Data_shift: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundWindow: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundWindow: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Data_window: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Data_window: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundSpan: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundSpan: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundSpan_add: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundSpan_add: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_phase: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_phase: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1At: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1At: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Window_frame: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Window_frame: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Data_stateCell: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Data_stateCell: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_prepare: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_prepare: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Buffer_reads: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Buffer_reads: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_payload: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_payload: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Buffer_suffix: axioms: [propext,
 Quot.sound]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Buffer_suffix: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_restore: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_restore: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_lookup: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_lookup: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_canonical: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_canonical: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundRep: axioms: [propext]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundRep: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundRep_entry: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1RoundRep_entry: direct sorryAx users in closure: []
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_effect: axioms: [propext,
 Quot.sound,
 Classical.choice]
_private.TCSlib.Complexity.TuringMachine.CodeSimulator.0.Turing.MachineFormat.h1Round_effect: direct sorryAx users in closure: []
PASS 98 new private declarations: only propext/Classical.choice/Quot.sound; no admissions
```

## Archive and replay

`fill-b5a-h1-cont.zip` contains this `REPORT.md`, the full modified source under its repository path, one `git format-patch` commit against the recorded base, `tcslib-fill-b5a-h1-cont.bundle`, `final-sweep.log`, `axioms.log`, all probes and relevant before/after evidence, and `SHA256SUMS`. The bundle is incremental and requires the recorded base. No olean or dependency cache is needed in the delivery; all final oleans were produced by the check script.

The patch was replayed into a separate temporary git index initialized at the base; its resulting tree equals the delivery commit's tree. This verification did not check out or modify another branch. `git bundle verify` and all archive-entry checksums passed. `evidence/replay.log` and `evidence/package-verification.log` record those checks. To integrate, use the format-patch series with the campaign's normal `git am -3` procedure on a maintainer-controlled integration branch, then repeat the checks as required by `workflow.md`.

The runtime shim is environment-specific and optional. `evidence/verification.log`, `freeze.log`, probe logs, and source snippets allow the claimed freeze, exact statement probes, and admission set to be reviewed independently. Development logs are explicitly separate from the final gates. No unreported proof gap or claimed physical H1 remains hidden in this partial.
