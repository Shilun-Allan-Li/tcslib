/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Configuration
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.NondeterministicSpace
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Oracle
import TCSlib.Complexity.TuringMachine.OracleFinite
import TCSlib.Complexity.TuringMachine.OracleNondeterministic
import TCSlib.Complexity.TuringMachine.OracleAgreement
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.BufferWords
import TCSlib.Complexity.TuringMachine.Sweep
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.UnaryTape
import TCSlib.Complexity.TuringMachine.CounterProg
import TCSlib.Complexity.TuringMachine.CounterProgRun
import TCSlib.Complexity.TuringMachine.CounterProgInput
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Build.Wrappers
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Zone
import TCSlib.Complexity.TuringMachine.Build.ZoneTape
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.OracleCall
import TCSlib.Complexity.TuringMachine.SymbolLift
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.Build.InputWindow
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.Scan
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.Build.CfgRecord
import TCSlib.Complexity.TuringMachine.Build.InputLength
import TCSlib.Complexity.TuringMachine.Build.RecordTable
import TCSlib.Complexity.TuringMachine.Build.CertShell
import TCSlib.Complexity.TuringMachine.Build.OracleSim
import TCSlib.Complexity.TuringMachine.Build.Contract
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.WindowRun
import TCSlib.Complexity.TuringMachine.Build.InputDevice
import TCSlib.Complexity.TuringMachine.Build.StepBlock
import TCSlib.Complexity.TuringMachine.Build.StepBlockLoop
import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
import TCSlib.Complexity.TuringMachine.CodeSimulator
import TCSlib.Complexity.TuringMachine.ChoiceWords
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.TuringMachine.Robustness.Bidirectional
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSchedule
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousCandidate
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSetup
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousLedger
import TCSlib.Complexity.TuringMachine.Robustness.Oblivious
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.CodeParser
import TCSlib.Complexity.TuringMachine.CodeFormat
import TCSlib.Complexity.TuringMachine.Codes2Tape
import TCSlib.Complexity.TuringMachine.MathlibBridge
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.UniversalK
import TCSlib.Complexity.TuringMachine.SelfUniversal
import TCSlib.Complexity.TuringMachine.UniversalInterpreter
import TCSlib.Complexity.TuringMachine.UniversalBlock
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.NDCodeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Complexity — Turing machines

The multi-tape Turing machine model underlying the Arora-Barak formalization
(see `AroraBarakChapter1Plan.md`): a machine-free configuration/action layer, the
deterministic machine with time and space semantics, the bundled finite layer over which
all complexity classes are stated, and oracle machines as a wrapper over the same
configurations.

The core model files are vendored from cslib
(https://github.com/leanprover/cslib, commit a3747758, 2026-09-14); see the file headers
for the local modifications.

## Contents

* `CodeFormat` — shared transition-record and table-format parsers, with the one-tape instance.
* `Codes2Tape` — the deterministic two-work-tape code scheme (§13, Z3), an instance of
  `CodeFormat`, with its uniform scheme from `CodeSimulator`.

* `Configuration` — configurations `Cfg`, actions `Action` and their application; the
  space measure. Nothing here mentions a machine (vendored).
* `Deterministic` — `MultiTapeTM`, the step/run semantics, time and space bounds
  (vendored).
* `StateRenaming` — transport of actions, configurations, and machines along maps
  of the state type; shared by the oracle embedding and the code normal form.
* `Finite` — the bundled `FinTM` layer carrying `Fintype`/`DecidableEq` state instances;
  all headline definitions are stated over it.
* `Nondeterministic` — binary-choice nondeterministic machines [AB09, §2.1.2]:
  choice-word run semantics, all-branch halting, the bundled `FinNDTM` layer, the
  deterministic embedding, and the run-level transfer, slice, relabelling and input-locality
  lemmas (the classes live in `ClassNP/NTIME`).
* `NondeterministicSpace` — the space measure of binary-choice NDTMs along choice-word
  runs: visited cells, as for the deterministic `SPACE` [AB09, Definition 4.1].
* `ChoiceReplay` — choice-tape determinization: the replay machine of an NDTM, which reads its
  choices from an extra work tape, and the replay lemma [AB09, §2.1.2, Theorem 2.6]. Proved.
* `Oracle` — oracle machines `OracleTM` [AB09, §3.4]: same configurations, oracle-dependent
  step; the embedding of plain machines and its oracle-independence sanity theorems.
* `OracleFinite` — the bundled finite layer `FinOracleTM`, carrying well-formedness as a
  field, over which the oracle classes are stated [AB09, Definition 3.5].
* `OracleNondeterministic` — nondeterministic oracle machines [AB09, Definition 3.4], for
  `NPOracle` and the relativization theorem.
* `OracleAgreement` — oracle locality: runs under oracles agreeing on every submitted
  string coincide [AB09, Theorem 3.7].
* `NDCodes` — codes for nondeterministic machines [AB09, §1.4, §3.2]: the two-work-tape
  coded normal form, its fixed serialization, and the scheme laws with the effective
  (canonizer) form.
* `NDCodeSimulator` — the interpreter core for nondeterministic codes (C1): the serialization
  bridge, the per-code replay canonizer and the core `R` [AB09, Exercise 2.6]. The core is
  proved; the canonizer is sorried.
* `Simulation` — generic machine-construction gadgets: emission chains, control
  actions, disjoint tape-block embeddings with lockstep run lemmas, the input-head
  rewind, and the two-machine branch union.
* `BufferWords` — the cells of a buffer tape holding a composite word: a suffix at an offset, a
  middle word's letters, prefixes and suffixes, the blank cells off the word, and a unary word
  with its terminator. Proved.
* `Sweep` — the generic zipper/transduction layer for sweep-based tape
  simulations, with the initialized-run head/support bound.
* `Composition` — identity/constant machines and closure of time-bounded computability
  under composition; also the formal home of the append-only-output convention
  argument.
* `UnaryTape` — work tapes holding a number in unary.
* `CounterProg`, `CounterProgRun` — counter programs (goto programs over unary registers)
  compiled into machines, with Hoare-style run lemmas; the model of the polynomial-time
  emitters of [AB09, Remark 6.7] (polynomial time: `ClassNP/CounterProgPolyTime`).
* `Build/Embed`, `Build/Seam`, `Build/Catalog` — the §12 routine layer
  (`machine-library-design.md` §12, gate closed round 3): the bank-embedding
  transformers with their returning flavors, seam composition with the
  general-configuration forms and the release adapter, and the space-annotated
  catalog rows.
* `Build/NDHost` — the nondeterministic phase host over NDTM phases and the choice writer, for
  the guess-first route of the nondeterministic time hierarchy (C1). Proved, the writer's
  bounded contract included (C1-W, 2026-10-17).
* `Build/VirtualInput` — virtual-input hosting (`machine-library-design.md` §13, Z1): a
  machine whose input is a buffered work-tape word runs inside a host, one step per step.
* `Build/Zone` — the pure zone layer (§13, Z2, as revised by §13d): zone contents, the
  guarded pairwise ops, the cascade and its mirror, the scanned index, the total rebalance,
  the extension by one level, and the virtual tape a track represents.
* `Build/ZoneTape` — the multi-track zoned carrier over `ZoneSym k` (§13d, G3): the layout
  with blank separators, the inner-packed encoding `zonedTape` and its invariants.
* `Build/ZoneRebalance` — the rebalance and extension rows (§13d, G4), as contracts;
  sorried for the G4 fill.
* `Build/OracleCall` — the oracle-machine rows (`machine-library-design.md` §12.9):
  W1 capture onto the query tape, landing in `qQuery`, and the two-step answer tail.
* `SymbolLift` — the embedding transport (`machine-library-design.md` §12.8, R8.0): a
  `Bool` machine run on a richer alphabet along `e : Bool ↪ Γ`, with time and space
  unchanged.
* `Build/CounterLoop` — the counter-driven loop (§12.7) and the pattern expansion
  `expandTM` (§12.8, R8.6).
* `Build/InputWindow` — the counter-driven copy of a bounded window of the native input onto a
  work tape, for the nondeterministic time hierarchy [AB09, Theorem 3.2]. Proved.
* `Build/SeamLayout` — the step block's table and summary tapes from a captured serialization,
  the one redistribution the step-block startups cite. Proved.
* `Build/Rewind` — the rewind of a work-tape head to the start of a word, from any cell of the
  word or just past it, the empty word included. Proved.
* `Build/Scan`, `Build/InputCall`, `Build/CfgRecord` — the §12.8 rows, with the field
  layout, compare, seeks and two-pass scan in `Build/Catalog`'s Part 3: the constant and
  advancing writers and the native-input copy and fold; the input call and input seek;
  the rich configuration-record carrier and the record rows. All proved (§12.8 fill gate
  closed).
* `Build/InputLength`, `Build/RecordTable` — the deferred §12.8 rows (`machine-library-design.md`
  §12.8b): the input length `Nat.bits |x|` (R8.5c), and the table layer over records (header,
  sentinels, find, append, template, init, validity, odometer next, the end-to-start adapter).
  Fills in progress; each module's header carries its status.
* `Build/OracleSim`, `Build/CertShell` — oracle-call simulation (§12.10, the B1b extension): one
  plain host simulating an oracle machine with queries answered by a plain decider, the
  choice-word machine of an oracle NDTM, and the plain certificate shell. Fills in progress;
  each module's header carries its status.
* `Build/StepBlock` — the step block (host H2, `machine-library-design.md` §14): one finite
  machine per work-tape count `k` that performs one simulated transition of a `k`-tape
  binary table held as data, with its contract `Turing.StepBlock.roundTM_effect`, the
  record skipper and fixed-field reader, the per-round space ledger and the cofinal
  iteration. Proved; promoted from `CodeSimulator` (H2-S gate closed, round 2).
* `Build/StepBlockLoop` — the step block's counter loop (host H2's loop form, H2-L,
  `machine-library-design.md` §14): the binary deadline clock over the step block, native and on
  a buffered input, from any represented live start, with its early-escape bound and live
  exits. Proved; harvested from `CodeSimulator` (H1 harvest gate passed, 2026-10-14).
* `Build/StepBlockForward` — the step block's forwarding round loop (host H2's unclocked loop form,
  H2-F, `machine-library-design.md` §14): any `k`-tape table simulated in macro-step lockstep with
  its emissions forwarded, per-step cost bounded by the table's length, and a space ledger.
  Statement gate passed 2026-10-15; the contract is sorried.
* `CodeSimulator` — the format-parameterized uniform simulator over item 8's code formats
  (B5a): one bounded-acceptance interpreter and canonizer whose one- and two-tape instances are
  the EXPCOM and Codes2Tape code schemes. Fills in progress; the module header carries its
  status.
* `ChoiceWords` — certificate and choice words: split uniqueness for length-determined
  suffixes, the exact NP certificate length's monotonicity, the choice budget, and the
  truncation of halted branch runs. Shared by the plain Theorem 2.6, the oracle simulation's
  choice-word law and the certificate shell (wave-1 statement gate, round 1).
* `CounterProgInput` — transport a counter-program run past an input prefix
  that has already been consumed.
* `Build/Contract` — the framed-contract library (MIG-0a and MIG-0b, `machine-library-design.md`
  §16a), the facade of `Build/Contract/{Basic,Seam,Embed,Catalog,Lift}`: exact time, an endpoint
  function, an exit set with a no-earlier-exit cut and head envelopes, a derived frames layer,
  the compositions `trans`, `seq`, `inPhase`, `embed`, `branch` and the releases as thin
  wrappers over the public rows, and the segment, round and joint-trajectory layers with state
  renaming and the macro-step lockstep. The core, `Build/Contract/Basic`, imports only the
  machine core. Proved; the MIG-0a and MIG-0b gates closed.
* `Build/StepClock`, `Build/WindowRun` — host H3 (`machine-library-design.md` §14): the
  step-clocked runner, shared with the nondeterministic time hierarchy; the semantic windowed
  run `windowRun`; the windowed round loop and the step-clocked windowed runner. Statement gate
  passed 2026-10-14; the specification is proved, the machine contracts are sorried.
* `Build/InputDevice` — host H5: the input-device interface, the native device, and the
  bounded-prefix ruler device with its boundary test, call rows and host. Proved.
* `Build/Convention`, `Build/Wrappers`, `Build/Loop`, `Build/Primitives` — the
  machine-construction library (`machine-library-design.md`): the `Cfg.ofWords` seam
  discipline, the capture/silence and halt-redirect wrappers with the timed branch,
  the bounded-loop combinator, and the primitive catalog of timed string functions.
  Proved, and audited at the shared-infrastructure gates.
* `Robustness/AlphabetReduction` — binary alphabet suffices [AB09, Claim 1.5].
* `Robustness/SingleTape` — one work tape suffices, quadratically [AB09, Claim 1.6].
* `Robustness/Bidirectional` — unidirectional tape use suffices [AB09, Claim 1.8].
* `Robustness/Oblivious` — oblivious machines and the quadratic oblivious simulation
  [AB09, Remark 1.7, Exercise 1.5] (imports the `ClassP` definitions it needs).
* `Encoding` — machines as strings [AB09, §1.4]: the code normal form `CodeTM`, the
  fixed canonical serialization, the representation-scheme laws `MachineCode`, and
  the effective scheme `EffectiveMachineCode` that the universal machine requires.
* `Universal` — the universal machine [AB09, Theorem 1.9]: the all-string evaluator
  with linear overhead and divergence preservation, the relaxed quadratic
  total-function form, and the time-bounded variant (code-first input layout).
* `UniversalK` — the `k`-generic universal machine (U2) [AB09, Theorem 1.9]: the `k`-tape
  scheme interface `EffectiveCodeK` with the one- and two-tape schemes as instances, the startup,
  the self-application universal machine with time and space ledgers, and the code-first
  evaluator. Statement gate passed 2026-10-15; the three contracts are sorried.
* `SelfUniversal` — the self-application universal machine `U₀` and its startup
  [AB09, Exercise 4.1], the universal machine of the space hierarchy's window route.
  Statement gate passed 2026-10-14; both are the `k = 1` cases of `UniversalK`'s statements.
-/
