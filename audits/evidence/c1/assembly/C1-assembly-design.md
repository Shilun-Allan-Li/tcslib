# C1-A design note: the guess-then-run assembly lemma

Read-only design note on the campaign tip `e831b5b0d887dac3bbf1aa2c19af28983b15b982` (records;
its Lean content is that of `13a16a69`, after MIG-0b's landing, PR #90, and PR #91). Sources: the
tip's tree, extracted by `git archive` into the gate folder's `base/`; olean snapshot
`oleans-lm0b`, MIG-0b's replay output (`logs/base.log`). The work began at `2c3c975a` with
`oleans-lc1`; every check was re-run at the new tip, and every `file:line` below is the tip's.
Paths are relative to the repository root unless they name the gate folder. Conventions as in the C1 design note: **VERIFIED** means read in the code at the cited
`file:line` or checked by elaboration (logs in the gate folder); **INFERRED** is a conclusion not
checked by elaboration; **ESTIMATE** marks size figures that are forecasts, **MEASURED** those
counted.

The unit this note designs is `C1Assembly.lean` (896 lines, MEASURED). It elaborates with
0 errors and 0 warnings, and every theorem in it is **proved**; the six that pass the writer are
proved modulo the writer's gated contract `Turing.ndWriterTM_run_block`, which stays sorried
(VERIFIED: `logs/elaboration.log`, `logs/axioms.log`).

---

## 0. Summary

1. **Why the lemma exists.** Ruling 2 of the C1 host-contracts gate
   (`audits/c1-hosts-statements-findings.md`, open question 2; resolutions, "Rulings") asks for a
   public guess-then-run assembly lemma in `Build/NDHost.lean`, stated and gated in C1-A before
   the brief of the universal NDTM `UN`. Note N3 and the `phaseHostND_run` row of the same
   findings say the same thing from the other side: `phaseHostND_run` is a one-phase result, and
   "concatenating phases is the disclosed future assembly lemma"; the transfer-and-phase-host
   ruling (brief point 8) warns not to mistake those lemmas "for the still-to-be-stated whole
   guess-then-run equivalence".
2. **The shape: one host, a small family of theorems.** `Turing.guessRunTM` is
   `Turing.NDTM.phaseHostND` over six fixed phases: a deterministic setup `P`, the bounded choice
   writer, a one-step skip and the catalog's `Turing.skipBackTM` (the rewind), a deterministic
   run `Q` ending in one of two live verdict states, and a one-transition verdict leaf. It is a
   composition of the present host with existing catalog rows, as the ruling requires. Eight
   theorems state its contract; §2.3 lists them.
3. **Everything is proved.** The family is proved by composing `Turing.NDTM.phaseHostND_run`
   (five times along a branch), `Turing.MultiTapeTM.toNDTM_runWith`,
   `Turing.NDTM.runWith_mapState_of_agreeOn_det`, the writer's contract, the two seek contracts
   and the silent embedding's lockstep. The only sorried dependency is
   `Turing.ndWriterTM_run_block` (isolated by an axiom-substitution probe, `logs/axioms.log` §2).
4. **The ruling's checklist** (§1.3) is met item by item: the writer's word is identified
   (`(w.drop (TP + 1)).take m`), the deterministic phases are transferred, dispatch, rewind and
   setup are in the exact time `TP + 2m + TQ + 11`, both directions of exact-budget acceptance
   and all-branch halting are theorems, the interpreter core's clean-bank, head and output
   precondition is the identity `Turing.guessRunCfg_clean`, live verdicts become the leaf's
   emission, and emission capture is `Turing.guessRunTM_silent_spec`'s silent embedding.
5. **Sufficiency is demonstrated** by two consumer probes (`AssemblyConsumerProbe.lean`): the
   frozen statement of `Turing.exists_timed_universal_NDTM` follows from
   `Turing.exists_ndInterpreterCore` and a setup hypothesis (UN's remaining fill obligation),
   and the `Complexity.NTIME (g + 1)` membership shape of the diagonalizer `D` follows from a
   setup and suffix hypothesis.
6. **One new import.** `Build/NDHost.lean` gains `import TCSlib.Complexity.TuringMachine.Build.Catalog`
   for the rewind rows. `Build.Catalog` does not have `Build.NDHost` in its closure, and the only
   importer of `Build.NDHost` is the `TCSlib.Complexity.TuringMachine` facade, which already
   imports `Build.Catalog` (VERIFIED, `logs/names.log`).

---

## 1. What UN and D need from "guess, then run"

### 1.1 The universal NDTM (statement 1, `Diagonalization/NTimeHierarchy.lean:159-164`)

Its statement: for every effective scheme `c`, one `UN : FinNDTM Bool` such that for every code
`α` there is `C` with, on `z = ⟨⟨bits t, α⟩, x⟩`, `UN.tm.HaltsWithin z (C·(t + 1))` and
`UN.AcceptsWithin z (C·(t + 1)) ↔ (c.decode α).toFinNDTM.AcceptsWithin x t`. Its sketch
(`:116-158`): parse the header and expand `t` into a unary block on a stream tape; the bounded
writer overwrites the block with `t` choice bits in `t + 1` steps on every branch; rewind the
stream head (`Turing.skipBackTM`); then the deterministic core `Turing.exists_ndInterpreterCore`
on the guessed stream. "The assembly is the nondeterministic phase host … over a deterministic
prefix, the writer and the deterministic core"; "`UN` accepts iff some guessed `s` is an
accepting branch of length `t`"; the guess-then-run assembly is a named fill obligation.

What the assembly must deliver for UN (VERIFIED against `NDCodeSimulator.lean:128-145`, the
core `R`):

| Need | Why |
|---|---|
| the stream on the core's tape `j` is exactly the writer's `t` bits | `R` reads `s.take t`; acceptance is "some `s` of length `t`" |
| every branch of `UN` is the deterministic runs of the setup and of `R` | only the writer may branch |
| exact time: setup + guess + rewind + dispatch + core + verdict | `HaltsWithin` and `AcceptsWithin` are exact-length (`Nondeterministic.lean:205`, `ClassNP/NTIME.lean:93`) |
| `R`'s start configuration: input head on the first symbol, `s` on tape `j` from cell `0`, every other tape blank, every head at `0`, empty output | `R`'s `start` (`NDCodeSimulator.lean:134-136`) |
| `R`'s verdicts are **live** states `accept`/`reject`, reached at `T`, none before | a live verdict is not a halt: something must halt with output exactly `[true]` |
| `R`'s contract says nothing about `R`'s output | its emissions must be captured, or `UN`'s output is not `[true]` |
| `T ≤ C·(t + 1)` for every stream | uniform budget `C·(t + 1)` for all-branch halting |

### 1.2 The diagonalizer (statement 4 (iii), `NTimeHierarchy.lean:284-312`)

Its sketch: right after computing `g n` (by `g`'s witness), `D` guesses a stream of `g n` bits
with the bounded writer, its only nondeterministic phase; every later phase is deterministic
(the locator, the materialization of `⟨⟨bits (g n), αⱼ⟩, 1^{n+1}⟩`, the core under Z1 and the step
clock, `BF` at the top rung with the flip); branches cut by the countdown reject; non-unary inputs
reject; "`D ∈ NTIME (g + 1)` by construction"; `L(D)` is read per rung.

What the assembly must deliver for D: the same branch identification and transfer, with a
**generic** deterministic suffix whose handoff configuration is *not* clean (it still holds
`bits (g n)` and whatever else the setup left), live verdicts (accept, reject, timeout-reject),
a uniform verdict-time bound `≤ c·(g n + 1)` for all streams, and a way to reject malformed
inputs without guessing. `BF` emits its verdict, so `D` captures its emissions inside the suffix;
the assembly must therefore state acceptance with the suffix's output made explicit.

### 1.3 Ruling 2, item by item

| Ruling 2 asks | Where it is met |
|---|---|
| identify the writer's word | `guessRunTM_runWith_handoff`: the stream is `(w.drop (TP + 1)).take m` |
| transfer the deterministic phases | every theorem: setup and run are `toNDTM` phases; their branches are their `runFrom` (`phaseHostND_run`, `toNDTM_runWith`; `runWith_mapState_of_agreeOn_det` for a halting setup) |
| account for dispatch/rewind/setup | the handoff time `TP + 2m + 9` (four dispatches, `m + 1` writer, `1` skip, `m + 3` rewind) and the halting time `TP + 2m + TQ + 11` |
| both directions of exact-budget acceptance | `guessRunTM_accepts_iff` (an iff at every budget `B ≥ TP + 2m + T + 11`) |
| all-branch halting | `guessRunTM_haltsWithin` |
| `R`'s clean-bank/head/output precondition | `guessRunCfg_clean`: from a clean setup, the run's entry is `R`'s start, silently embedded |
| live verdicts | `acc`/`rej` are live states of the run, redirected to the verdict leaf, which emits the bit and halts |
| emission capture | `guessRunTM_silent_spec` runs `R` as `embedSilentTM ι cap R`; the generic `accepts_iff` keeps the run's output in its right side |
| composition of the present host, no new architecture | `guessRunTM := phaseHostND …` (§2.1); every phase is an existing machine except the one-transition leaf (§2.2) |

---

## 2. The design

### 2.1 The host

```
guessRunTM P pexit j Q qentry acc rej := NDTM.phaseHostND (guessRunPhases P j Q) ⟨.pre, P.q₀⟩
  (guessRunRed pexit qentry acc rej)

phase   machine                                        redirect at
pre     P.toNDTM                                       pexit        ↦ ⟨guess, run ()⟩
guess   ndWriterTM k j () (fun _ _ => ()) (fun _ => false) true    done ↦ ⟨skip, run⟩
skip    (skipTM k j).toNDTM                            done         ↦ ⟨back, run⟩
back    (skipBackTM k j).toNDTM                        done         ↦ ⟨run, qentry⟩
run     Q.toNDTM                                       acc ↦ ⟨out, true⟩, rej ↦ ⟨out, false⟩
out     state b: emit b, halt (either choice)          —
```

* **Why the rewind is two seeks.** The bounded writer stops *on* the blank after the block,
  without moving (`ndWriterTM_run_block`, `Build/NDHost.lean:177-189`). `Turing.skipBackTM`
  returns from the first cell of a field to the first cell of the previous one
  (`Build/Catalog.lean:11785`, contract `:11809`): it needs the head one cell past the blank.
  One `Turing.skipTM` step over the empty word (`:11704`, contract `:11724`) puts it there. The rewind then needs a
  blank just before the block (hypothesis `hleft`), which the clean setup provides. Its cost is
  `1 + (m + 3)`. Head positions are then exactly the setup's: the entry configuration
  `guessRunCfg cP j s qentry` keeps `cP.workTapePos`.
* **Why a verdict leaf.** The phase host's redirect is one silent, stationary step to a *state*
  (`Build/NDHost.lean:70-77`); nothing in it halts or emits. The verdict needs one transition that
  emits a bit and halts. No public emit-and-halt row exists for plain machines
  (`Turing.OracleTM.answerAction`, `Build/OracleCall.lean:89`, is the oracle machines' one, on
  `k + 1` tapes); the transition is written inline in `guessRunPhases`, as in the library's
  hand-built deciders, and the docstring says so (policy §1, construction reuse).
* **Why the setup and the run are single machines.** Each is any deterministic `MultiTapeTM`,
  itself a composite of the deterministic layer (`Turing.phaseHostTM`, the seams, `embedSilentTM`,
  Z1, the step clock). The nondeterministic assembly then has one fixed architecture, shared by
  UN and D; nothing nondeterministic is ever composed twice.
* **Rejection without guessing.** A setup that halts before its exit halts the host with its own
  output (`guessRunTM_runWith_setup_halt`); `D` can also reject a malformed input through an empty
  block and a rejecting run.

### 2.2 Configurations

* `guessRunCfg c j s q` (`C1Assembly.lean:207-213`): `c` in state `q`, with the `|s|` cells of
  tape `j` from its head overwritten by `s`; every head unchanged.
* `streamStartCfg z j q s` (`:219-221`): the core's `start` of `NDCodeSimulator.lean:134-136`,
  verbatim (state `q`, input head `1`, `bufferTape s` on tape `j`, blank elsewhere, heads `0`,
  output `[]`).

### 2.3 The statement family (all in `C1Assembly.lean`; all proved)

| Theorem (line) | One-line meaning |
|---|---|
| `guessRunTM_runWith_handoff` (257) | every word of length `TP + 2m + 9` reaches the run's entry `guessRunCfg cP j ((w.drop (TP + 1)).take m) qentry` |
| `guessRunTM_runWith_live` (435) | every shorter word leaves the host live |
| `guessRunTM_runWith` (470) | a word with stream `s`, of length `≥ TP + 2m + TQ + 11`, halts with the run's configuration at its first verdict and output `d.output ++ [verdict = acc]` |
| `guessRunTM_runWith_setup_halt` (563) | a setup that halts before its exit halts the host unguessed (proved; no writer) |
| `guessRunTM_haltsWithin` (609) | if every stream's first verdict comes within `T`, all branches halt within `TP + 2m + T + 11` |
| `guessRunTM_accepts_iff` (642) | at every `B ≥ TP + 2m + T + 11`: an exact-length-`B` branch halts with `[true]` iff some stream's first verdict is `acc` with empty output |
| `guessRunCfg_clean` (715) | a clean setup's handoff is `embedSilentCfg ι cap blank 0 [] [] (streamStartCfg z jR entry s)` (proved; no writer) |
| `guessRunTM_silent_spec` (808) | with `R` run silently and a clean setup: all-branch halting, and acceptance iff some stream's first `R`-verdict is `acc` |

The setup hypotheses are explicit and repeated (the setup's run reaches `pexit` first at `TP`,
a nonblank block of `m` cells from the head of tape `j`, blanks just after and just before), so
each statement reads on its own; no bundling predicate is introduced.

**Exact budgets.** `HaltsWithin` and `AcceptsWithin` quantify over words of length exactly the
budget. The family states them at every budget at least the uniform bound, which is what both
consumers use (`C·(t + 1)` for UN; `c·(g n + 1)` for D). A per-stream budget form (accept within
`B` iff some stream's verdict time `TQ` has `TP + 2m + TQ + 11 ≤ B`) follows from
`guessRunTM_runWith` and `guessRunTM_runWith_live` but is not stated: no consumer needs it.

**Layering.** The conclusions are stated on `NDTM.runWith` and `NDTM.HaltsWithin`, not on
`FinNDTM.AcceptsWithin`: `TuringMachine/` modules do not import `ClassNP` (the C1 host-contracts
gate's layering, approved). The acceptance shape `∃ w, w.length = B ∧ halted ∧ output = [true]` is
`FinNDTM.AcceptsWithin` unfolded (`ClassNP/NTIME.lean:93-96`); probe 1 uses it by `unfold`.

### 2.4 Alternatives considered

* **The suffix halts with an output, no verdict states** (design note §3.1's sketch: "`Q` accepts
  from the configuration with `s` written"). Rejected: the core `R` ends in live verdicts, so a
  verdict-to-halt step is needed somewhere, and the ruling asks the assembly to handle it.
* **The rewind inside the suffix.** Then the handoff would have the stream head at `m`, and the
  core's precondition would not hold at the handoff; the ruling asks the assembly to account for
  the rewind and to establish that precondition.
* **The slice lemma instead of the phase lemma.** `Turing.NDTM.runWith_eq_fixChoice_runFrom`
  (`Nondeterministic.lean:401`) needs both transition functions to coincide at every visited
  state; that fails at the writer's live states, so it covers only the deterministic segments.
  `phaseHostND_run` covers every phase, the writer included (its guard is the writer's "no
  shorter word reaches `done`"), and the proofs use it throughout. `phaseHostND_fixChoice` is not
  needed.
* **`Contract`-form statements** (MIG-0a, `Build/Contract.lean`). Not used: the phases' contracts
  are run equalities at the configuration level, which the existing rows already give, and the
  host's own statements are about branches of an NDTM, which `Contract` (deterministic) does not
  describe. `Contract.toND` stays with MIG-0b, as the C1 design note §3.1 proposed.
* **Capture built into the generic host.** The generic run `Q` is any machine; capture is the
  caller's composition (`embedSilentTM`), stated for the core in `guessRunTM_silent_spec`. D's
  suffix captures `BF`'s emission in its own deterministic composition.

### 2.5 What the consumers still owe (fill obligations, not new hosts)

* **UN's setup** (probe 1's hypothesis `hsetup`): a deterministic machine on some `k ≥ K + 1`
  tapes that, on `⟨⟨bits t, α⟩, x⟩`, reaches its exit first within `C_P·(t + 1)`, with the input
  head back on the first symbol, a nonblank block of exactly `t` cells on tape `ι jR` from cell `0`,
  every other tape blank, every head at `0`, empty output. INFERRED buildable from existing rows
  (the header's first component, `Turing.expandTM` at `Build/CounterLoop.lean:1534`, clears and
  the input rewind); its cost is `O(|bits t| + t + 1)`.
* **D's setup and suffix** (probe 2's hypotheses): the setup reaches its exit with the block of
  `g n` cells (or an empty block, or halts, for malformed inputs); the suffix reaches a verdict
  within `c·(g n + 1)` on every stream.

---

## 3. Every cited public declaration (VERIFIED at the tip)

| Declaration | file:line | Use |
|---|---|---|
| `Turing.NDTM.phaseHostND` | `TuringMachine/Build/NDHost.lean:70` | the host |
| `Turing.NDTM.phaseHostND_fixChoice` | `Build/NDHost.lean:81` | not used (§2.4) |
| `Turing.NDTM.phaseHostND_run` | `Build/NDHost.lean:94` | each phase of a branch |
| `Turing.NDWriterState`, `Turing.ndWriterTM` | `Build/NDHost.lean:138`, `:154` | the guess phase |
| `Turing.ndWriterTM_run_block` (sorried) | `Build/NDHost.lean:177` | the writer's branch and guard |
| `Turing.NDTM.runWith_mapState_of_agreeOn` | `TuringMachine/Nondeterministic.lean:339` | inside `phaseHostND_run` |
| `Turing.NDTM.runWith_mapState_of_agreeOn_det` | `Nondeterministic.lean:368` | the halting setup |
| `Turing.NDTM.runWith_eq_fixChoice_runFrom` | `Nondeterministic.lean:401` | not used (§2.4) |
| `Turing.MultiTapeTM.toNDTM`, `…toNDTM_runWith` | `Nondeterministic.lean:249`, `:266` | deterministic phases |
| `Turing.NDTM.runWith_append`, `runWith_cons`, `runWith_of_halt` | `Nondeterministic.lean:161`, `:156`, `:193` | word algebra, absorption |
| `Turing.NDTM.HaltsWithin`, `HaltsWithin.mono` | `Nondeterministic.lean:205`, `:215` | statements, probes |
| `Turing.FinNDTM` | `Nondeterministic.lean:232` | probes |
| `Turing.SeekPhase`, `Turing.skipTM`, `Turing.skipTM_run_ofCfg` | `TuringMachine/Build/Catalog.lean:11652`, `:11704`, `:11724` | the step right |
| `Turing.skipBackTM`, `Turing.skipBackTM_run_ofCfg` | `Build/Catalog.lean:11785`, `:11809` | the rewind |
| `Turing.embedSilentTM`, `Turing.embedSilentCfg` | `TuringMachine/Build/Embed.lean:248`, `:203` | capture |
| `Turing.embedSilentTM_runFrom`, `Turing.embedSilentTM_frame` | `Build/Embed.lean:363`, `:385` | capture's lockstep and frame |
| `Turing.embedSilentCfg_selected_tape`, `…_selected_pos` | `Build/Embed.lean:977`, `:986` | the clean handoff |
| `Turing.Cfg.mapState`, `Turing.Action.mapState` | `TuringMachine/StateRenaming.lean:81`, `:72` | tags |
| `Turing.FinTM.bufferTape` | `TuringMachine/Simulation.lean:494` | the stream on tape |
| `Turing.phaseHostTM`, `Turing.phaseHostTM_run` | `TuringMachine/Build/Seam.lean:832`, `:849` | the deterministic mirror (cited) |
| `Turing.exists_ndInterpreterCore` (sorried) | `TuringMachine/NDCodeSimulator.lean:128` | probe 1 |
| `Turing.FinNDTM.AcceptsWithin`, `…DecidesInTime`, `Complexity.NTIME` | `ClassNP/NTIME.lean:93`, `:119`, `:174` | probes |
| `Turing.exists_timed_universal_NDTM`, `Complexity.ntime_hierarchy` | `Diagonalization/NTimeHierarchy.lean:159`, `:341` | the consumers' statements |
| `Turing.OracleTM.answerAction` | `TuringMachine/Build/OracleCall.lean:89` | cited (no plain emit-and-halt row) |
| `Turing.expandTM` | `TuringMachine/Build/CounterLoop.lean:1534` | UN's setup (cited) |

The private body of `embedSlot` (`Build/Embed.lean:135`) is read, through `change`, in one proof
(`guessRunCfg_clean`, the capture tape's field), as `SpaceComplexity/Inclusions.lean:726`
(`b2b_capture_shape`) does; §5.

---

## 4. Sizes (MEASURED unless marked)

* The unit: 896 lines; the part as it lands: 849 lines; `Build/NDHost.lean` grows from 195 to
  1,064 lines (24 public and 2 private declarations; the campaign lint WARNs above 1,000 lines,
  and file size is not a driver under the user's standing decision).
* The C1 design note §3.1 estimated 200–400 lines; the difference is the six-phase host, the
  core interface (`guessRunCfg_clean`, `guessRunTM_silent_spec`), and the proofs themselves:
  425 nonblank lines of tactic proof (MEASURED: nonblank lines after each declaration's
  top-level `:= by`), of which 157 are the handoff's.

## 5. Risks and landing notes

* **The private slot search.** `guessRunCfg_clean` reads the capture tape's field of
  `embedSilentCfg` by unfolding the private `embedSlot`'s body (`List.find?`). A change to that
  body breaks the proof, not the statement. Recommended: a requested shared lemma
  `embedSilentCfg_cap` (the capture field of the transport, `cap ∉ range ι`) in `Build/Embed`,
  beside the selected-field exports, at the next shared-file window (MIG-0b's split, PR #90,
  added the R1 reconstruction exports to `Build/Embed` but no capture-field lemma).
* **The catalog rows.** `skipTM_run_ofCfg` and `skipBackTM_run_ofCfg` are R8.3 rows, not in
  MIG-1's deletion plan (INFERRED: no hit for the seek family in the MIG-1 round-2 gate folder or
  `audits/evidence/mig1`). If a later PR moves them, the import follows them.
* **Downstream.** No module but the facade imports `Build.NDHost`; the landing needs no replay
  beyond the facade's closure (INFERRED from the import graph; the landing PR's replay decides).

## 6. Sequencing against the open PRs

* **PR #92 (the B6 hosts, open).** No statement, proof or probe of this gate uses #92's
  statements: `Turing.exists_stepClockTMVia` is a dependency of the consumers' fills (D's suffix
  and `E`), not of the assembly, and the unit neither imports nor cites it. #92 patches two modules
  in the landed NDHost's closure, `StateRenaming` (two `relabelState` space lemmas added) and
  `Encoding`; the name screen covers #92's landing tree with no clash (`logs/names.log`). The two
  land in either order; if #92 merges first, the landing PR of this part re-runs the cut check at
  the merged tip (its replay snapshot was still being written during this run and was not used).
* **PR #93 (ARM comments and imports, open).** None of its 33 files is in the unit's closure or the
  probes' (`logs/names.log`); independent.
* **No other dependency.** The part waits on nothing but this gate; UN's brief waits on this gate and
  on the H1 hosted-clock harvest (C1 resolutions).
