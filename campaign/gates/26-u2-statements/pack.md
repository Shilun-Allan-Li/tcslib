# External audit pack — U2: the `k`-generic universal machine and its forwarding round loop (statement gate)

Campaign: the Arora–Barak chapters 3–4 plan, §2.1 (user decision CH34-Q3, 2026-10-08: Thm 3.1 at
`f log f` through Hennie–Stearns and a two-work-tape universal machine at linear overhead). The
design is `audits/evidence/u2/U2-design.md`; the user adopted its decisions (a)–(d) on 2026-10-14
(`backlog.md` RD-5):
- (a) B6's `U₀` and its startup are generalized to `k` before B6's `U₀` fill, with B6's
  statements kept verbatim as the `k = 1` corollaries;
- (b) H2-F becomes a public host, gated hosts-first;
- (c) no verdict-only variant;
- (d) Theorem 1.9 keeps the relaxed code quantifier.

**This gate audits the statements.** It covers one host (H2-F), three machine contracts (U2-S,
U2-U, U2-E) with their scheme interface, B6's two statements re-proved as corollaries, and one
promotion. The four contracts are sorried, each under a proof sketch. Everything else is proved.

| File (bundle path; `audits/evidence/u2/gate/…`) | Content |
|---|---|
| `landed/TCSlib/Complexity/TuringMachine/UniversalK.lean` (new) | the scheme interface `EffectiveCodeK`, its two instances, U2-S, U2-U, U2-E |
| `landed/…/Build/StepBlockLoop.lean` (+84 lines net) | H2-F: `forwardLoopCfg`, `exists_forwardLoopTM` |
| `landed/…/SelfUniversal.lean` | B6's `exists_selfStartupTM`, `exists_selfUniversal`, re-proved as the `k = 1` corollaries |
| `landed/…/Codes2Tape.lean` | the promotion `Code2TM.serialize_eq_serializeK` |
| `landed/TCSlib/Complexity/TuringMachine.lean` | facade: the import and three `## Contents` entries |
| `probes/U2Consumer.body.lean` | the consumer probe: the time hierarchy's chain to Diagonal Part 1's `SelfSimulator`, with G5 as a hypothesis |
| `logs/`, `scripts/` | every check (`summary.log`); `run.sh` re-runs them all, fail-closed |

**Base and provenance (maintainer).**
- **Base:** the merged campaign tip `fba93e7ecfdf15baa3b58fe275af4da8460966c6` (PRs #95–#97
  merged), exported read-only by `git archive`. The precheck verifies all 724 exported blobs.
  The tip at the last run was Lean-equal to it (`logs/precheck.log`).
- **Snapshot:** `oleans-ltip3`, the catch-up replay of the merged tip (its log ends with
  `# modules=152 failed=0`).
- **Tools:**
  - `lean` ran only through `tools/leanelab.sh`, with no olean written. Python ran only as
    `python3 -I`, with asserted edits. No lake, no network. Nothing outside the gate folder was
    written.
  - No colleague-owned file and no in-flight file was touched: B6 F1's `CounterLoop` and
    `SymbolLift`, F2's `WindowRun`, MIG-1 stage S's catalog files and `Encoding`, Diagonal
    Part 1.
- **Authorship:** a maintainer sub-agent wrote the files.

## The statements and their homes

| Statement | Home | Status | Role |
|---|---|---|---|
| `Turing.EffectiveCodeK k` (structure: `numStates`, `machine`, `canonizer`, `canonizerTime`, `canonizer_computes`), `EffectiveCodeK.toFinTM`, `EffectiveCodeK.ofSerialize` | `UniversalK` (new) | defined | the `k`-tape scheme: a total decoding into `k`-tape machines, and a canonizer computing `serializeK` in arbitrary time |
| `Turing.EffectiveMachineCode.toK` (`k = 1`), `Turing.EffectiveMachineCode2.toK` (`k = 2`), with `…toK_toFinTM` and `…toK_machine` (`rfl`) | `UniversalK` | proved | the received one-tape scheme and the Z3 two-tape scheme as `k`-tape schemes |
| **U2-S** `Turing.exists_selfStartupTMK k E` | `UniversalK` | **sorried** | the startup, ending at the step block's seam (B6's at `k` tapes) |
| **U2-U** `Turing.exists_selfUniversalK k E` | `UniversalK` | **sorried** | self-application: time `C · (t + 1)`, space `C · (s + 1)`, and the converse |
| **U2-E** `Turing.universalK k E` | `UniversalK` | **sorried** | code-first evaluator on `pairEncode α x`: time `C · (t + 1)`, no `|x|` term, and the converse |
| **H2-F** `Turing.StepBlock.forwardLoopCfg`, `Turing.StepBlock.exists_forwardLoopTM k` | `Build/StepBlockLoop` | encoding defined; contract **sorried** | the forwarding round loop: a `Turing.Lockstep` of every `k`-tape table through the encoding, per-step cost `≤ 50 · (\|tableBitsK\| + 1) + C`, space ledger |
| B6's `Turing.exists_selfStartupTM`, `Turing.exists_selfUniversal` | `SelfUniversal` | **re-proved** as `k = 1` corollaries (statements byte-identical) | the gated `U₀` |
| `Turing.Code2TM.serialize_eq_serializeK` | `Codes2Tape` | **promoted** (was the private `twoTape_serialize_eq`; statement and proof unchanged) | the two-tape serialization is `serializeK` |

**Naming.** H2-F's contract is `exists_forwardLoopTM`, not `exists_emitLoopTM`: the latter
already names `Turing.FinTM.exists_emitLoopTM` (`Build/Loop`, ten uses). The two would be
ambiguous under `open Turing.FinTM Turing.StepBlock`.

**No promotion is needed for one tape.** The public field `Turing.oneTapeMachineFormat.serialize_eq`
already states `CodeTM.serialize M = serializeK M.tm`, and B6's sketch cites it. So
`CodeSimulator` (B5a's file, with a continuation in flight) is not edited.

## B6's statements: re-proved in place (recommended), with the evidence

There were two options: keep B6's two statements sorried and add the generic ones beside them,
or re-prove B6's statements in place as corollaries. **This unit re-proves them in place.**

1. **The specialization is exact.** The generic startup lives on `K + (k + 2)` tapes, with the
   table at `j.val = k` and the summary at `j.val = k + 1`. At `k = 1` this is B6's
   `K + 3` tapes with `j = 1` and `j = 2`. The proof of `exists_selfStartupTM` (25 lines) unfolds
   only `Fin` numerals and `EffectiveMachineCode.toK_machine` (`rfl`). `exists_selfUniversal` (8 lines) drops the
   time clause and the converse, takes `t' := C · (t + 1)`, and weakens space by `s`. Both
   elaborate with no `sorry` of their own (`logs/elaboration.log`: the cut check reports no
   warning in `SelfUniversal`'s body).
2. **No statement moves.** The freeze shows both signatures byte-identical. The consumers'
   citations are unchanged: `space_hierarchy`'s and `space_universal`'s sketches in
   `SpaceComplexity/Hierarchy.lean` cite `exists_selfUniversal` and `exists_selfStartupTM` by
   name.
3. **No status regression.** Before, each carried `sorryAx` through its own `sorry`. After, each
   carries it through the generic contracts (`SelfUniversal.base` versus `SelfUniversal.cut` in
   `logs/elaboration.log`).
4. **One construction.** Keeping both would leave two sorried contracts for one machine. B6's
   `U₀` fill would then build the `k = 1` case separately, which is the duplication decision (a)
   rules out. With the re-proof, B6's `U₀` fill brief targets H2-F, U2-S and U2-U.

## `Turing.universal` at `k = 1` (U-1): the statement fits; the re-derivation is deferred

U2-E at `k = 1` with `E := c.toK` has `Turing.universal c`'s statement verbatim: the consumer
probe's `example`, whose type is copied from the tip, elaborates as `universalK 1 c.toK`.
Replacing `Turing.universal`'s proof now would make a sorry-free theorem depend on the sorried
U2-E. So it is **not** done here. It is the U-1 retrofit, after U2-E's fill.

## The consumer probe: the hierarchy's chain, with G5 as a hypothesis

`probes/U2Consumer.body.lean` is elaborated after Diagonal Part 1's landed body (as in its gate)
and the unit's `Codes2Tape` and `UniversalK` bodies. It contains:
- **`G5Interface`**, G5's function-level form, as a `Prop` hypothesis, never a `sorry`: every
  binary machine computing `f` within `T` has a two-tape equivalent within
  `c · (T + 1)(log₂(T + 1) + 1)`.
- **`twoTapeSelfSimulator hG5 : SelfSimulator logOverhead`.** It is built from U2-U at `k = 2`
  over `Classical.choice exists_effectiveMachineCode2`, which is sorry-free. Its normal form is
  G5 composed with the two-tape coding step (probe-local `exists_code2TM`) and the constant
  absorption `logOverhead_mul_le`.
- **`time_hierarchy_log hG5` and `time_hierarchy_book hG5`**, the book form under `n ≤ f n`.
  Both go through Diagonal Part 1's `DiagSimulator.time_hierarchy`.
- **Fit examples:** U2-E at `k = 1` is `Turing.universal`'s statement; U2-S, U2-U and U2-E at
  `k = 0`.
- **Cited-name checks** for every declaration the sketches name.

**Axiom result** (`logs/elaboration.log`):
- `exists_code2TM` and `logOverhead_mul_le` are standard.
- `twoTapeSelfSimulator` and the two theorems carry `sorryAx`. With G5 a hypothesis, the only
  source is U2-U.

## What is proved, what is sorried (MEASURED)

**Sorried, 4 contracts, each under a proof sketch:**
- `exists_forwardLoopTM` (H2-F);
- `exists_selfStartupTMK` (U2-S);
- `exists_selfUniversalK` (U2-U);
- `universalK` (U2-E).

**Proved or defined, standard axioms:**
- `EffectiveCodeK`, `toFinTM`, `ofSerialize`;
- both `toK`, both `toK_toFinTM`, both `toK_machine`;
- `forwardLoopCfg`;
- the promoted lemma;
- every received declaration of the four touched files except the two below.

**Proved, carrying `sorryAx` through the contracts:** B6's two statements.

Inherited and unchanged: `exists_uniformMachineCode2` keeps its `sorryAx` from `CodeSimulator`'s
open contracts, as before (at the base, three `sorry`s: `exists_canonDecider`,
`exists_canonGrammarStage` and `exists_uniformSimulator`).

## The freeze (MEASURED, `logs/freeze.log`)

| File | Received declarations | Changed | Header |
|---|---|---|---|
| `Build/StepBlockLoop.lean` | 10 | none (2 declarations appended) | identical |
| `Codes2Tape.lean` | 15 | `twoTape_serialize_eq` → `Code2TM.serialize_eq_serializeK`: private → public, signature identical, proof identical, docstring rewritten; the private `twoTapeMachineFormat`'s body re-points to the new name | identical |
| `SelfUniversal.lean` | 2 | both re-proved: signatures byte-identical, proofs (formerly `sorry`) and sketches replaced | gains `import …UniversalK` |
| `TuringMachine.lean` (facade) | 0 | three `## Contents` entries | gains `import …UniversalK` |

**No received proof became `sorry`, and no received signature changed.** The freeze's negative
controls (a changed signature, a proof made `sorry`, a visibility change) are reported as
failures.

## Cut checks per home (MEASURED, `logs/elaboration.log`)

The snapshot holds the base versions of the touched modules. Each home is therefore elaborated
against `oleans-ltip3`, with the landed bodies its imports need concatenated in front.

| Check | Contents | Sorry warnings, exactly at | Axioms |
|---|---|---|---|
| `StepBlockLoop.check` | the landed file (imports unchanged) | `exists_forwardLoopTM` | the 5 received publics and `forwardLoopCfg` standard |
| `Codes2Tape.check` | the landed file | none | as before, plus the promoted lemma standard |
| `UniversalK.cut` | Codes2Tape (landed), UniversalK | the 3 contracts | the interface and the instances standard |
| `SelfUniversal.cut` | Codes2Tape, UniversalK, SelfUniversal (landed) | the 3 contracts; none in `SelfUniversal` | both corollaries `sorryAx` (inherited) |
| `SelfUniversal.base` | the base file | its own two `sorry`s | `sorryAx` |
| `TuringMachine.cut` | Codes2Tape, UniversalK, SelfUniversal, the facade | the 3 contracts | — |
| `CodeSimulator.cut` versus `.base` | StepBlockLoop (landed), then `CodeSimulator` (its importer) | the baseline's plus `exists_forwardLoopTM` | identical to the baseline |
| `U2Consumer.cut` | Diagonal Part 1, Codes2Tape, UniversalK, the probe | the 3 contracts | as above |

There are 0 errors and no warning other than the expected `sorry` ones. A negative control
breaks the `k = 1` corollary's proof and checks that the `SelfUniversal` cut reports an error.

**Replay.** `replay-order.txt` lists 10 modules, topological, with no root `TCSlib`:
`Build/StepBlockLoop`, `CodeSimulator`, `Diagonalization/EXPCOM`, `Diagonalization/Relativization`,
the `Diagonalization` facade, `Codes2Tape`, `NDCodeSimulator`, `UniversalK`, `SelfUniversal`, and
the `TuringMachine` facade. Every import is listed earlier or present in `oleans-ltip3`.

## Names (MEASURED, `logs/names.log`)

**21 new public names.** In the screen they are covered by these components: `EffectiveCodeK`
(with its constructor and five fields), `ofSerialize`, `toK`, `toK_toFinTM`, `toK_machine`,
`exists_selfStartupTMK`, `exists_selfUniversalK`, `universalK`, `forwardLoopCfg`,
`exists_forwardLoopTM` and `serialize_eq_serializeK`. **No occurrence of any of them** appears in
the base tree's 723 Lean files.

## Duplication ledger (MEASURED, `logs/screen-*.txt`, `logs/screen-delta.log`; v2 screen, niced, one run at a time)

**Screen version.** The campaign's standard became the declaration-keyed v3
(`audits/evidence/retrofit/copy-text-screen-v3.py`) after these runs; it differs from v2 only in
telling apart same-named declarations of one file. No file of either population repeats a screened
short name, and the maintainer's v3 re-run equals both logs byte for byte from the counts line on
(`logs/screen-v3-check.log`).

**Population** (8 files, plus `UniversalK` after): `Build/StepBlockLoop`, `Build/StepBlock`,
`SelfUniversal`, `Codes2Tape`, `Encoding`, `UniversalStartup`, `Build/InputDevice`,
`CodeSimulator`.

**Result.** 37 pairs before, 41 after: **4 new, none gone.** All four are in `UniversalK`, and
none is proof material. They are disclosed here for the maintainer's acknowledgment:
1. `EffectiveCodeK` reproduces 89 of 127 characters (70%) of `Encoding.EffectiveMachineCode`,
   and the same of `Codes2Tape.EffectiveMachineCode2`. This is the shared field declarations
   (`canonizer : FinTM Bool`, `canonizerTime`, `canonizer_computes : canonizer.ComputesFunInTime …`).
   - These two received structures are already a 100% pair with each other (pre-existing).
   - The generic interface mirrors them by design.
   - Payback, if wanted: at U-1, restate the received schemes as views of `EffectiveCodeK`.
     That would change frozen chapter-1 surface; recommendation: acknowledge, no payback.
2. `EffectiveMachineCode.toK` and `EffectiveMachineCode2.toK` reproduce 84 characters (54–55%)
   of each other. This is the shared argument tail
   `c.decode c.canonizer c.canonizerTime c.canonizer_computes` of two one-line applications of
   the common constructor `EffectiveCodeK.ofSerialize`. The constructor was introduced to remove
   an 88% pair of the first draft. Recommendation: acknowledge.

The probe-local `exists_code2TM` (in the consumer probe, not landing material) mirrors
`Encoding.exists_codeTM_spaceUsed`'s relabelling proof. Its landing home and the dedup route are
an open question (Q4).

## Lint, widths, hygiene (MEASURED)

- **Lint:** `scripts/style_lint.py` finds 1 finding before and 1 after: the pre-existing
  `## Main definitions and results` heading of `Codes2Tape`. No new finding.
- **Widths:** every new or changed line is at most 100 characters (maximum 99).
- **Hygiene:** UTF-8, LF line ends, one final newline, no tabs, no trailing whitespace on new
  lines, no `#`-commands, the standard options.

## Known deviations (declared by the docstrings; verify)

- **`C` depends on the code string**, not only on the machine (Argument E), in U2-U and U2-E as
  in `Turing.universal`.
- **U2-U's space clause is measured at time `C · (t + 1)`.** After the halt the configuration is
  frozen, so this equals the space at the halt.
- **Theorem 1.9 at `T log T`** keeps the relaxed quantifier: the code is that of a normal-formed
  equivalent (decision (d); design note §4). U2-E's `k = 2` instance is its core.
- **No uniformity:** the canonizer's time is arbitrary. The hierarchy does not need uniformity:
  per-code constants with `clockTM` suffice (design note §1).

## Brief for the auditor

You are auditing the **trusted surface**:
- the definitions `EffectiveCodeK`, `toFinTM`, `ofSerialize`, both `toK` and `forwardLoopCfg`;
- the four sorried contracts;
- the claim that B6's two statements, `Turing.universal`'s statement at `k = 1`, and every
  received signature are unchanged.

The proved parts are machine-checked; do not review tactics for correctness. Hunt for:
1. **Unprovability.** For each sorried contract, argue in 2–5 sentences why it is true as
   stated, or exhibit a counterexample. Watch especially:
   - **H2-F's lockstep exactness:** `L.runFrom (enc c) (cost c) = enc (M.step c)` exactly, for
     every live `c`, including unreachable configurations with arbitrary tapes. Does the step
     block's contract support this? Is the encoding injective enough? Does the halting step
     land on the halted encoding?
   - **U2-U's space bound `C · (s + 1)`** with `s` the coded machine's cells, the startup's
     `B_α` included.
   - **U2-E's no-`|x|` time bound** through the ruler host.
   - **U2-S's endpoint**, an exact configuration: is every tape and head pinned down
     correctly at `k = 0`?
2. **Infidelity.**
   - Is `EffectiveCodeK` the right interface: is a total decoding with an arbitrary-time
     canonizer of `serializeK` exactly what the startup needs?
   - Do `toK`'s faithfully present the received schemes?
3. **Trivialization.**
   - Can `EffectiveCodeK` be inhabited degenerately so that U2-U is vacuous, for example a
     canonizer that never halts? (Its contract is `ComputesFunInTime`.)
   - Is `exists_forwardLoopTM`'s `C` unconstrained in a way that makes the bound empty?
4. **The corollaries.** Confirm that B6's statements and `universal`'s statement are recovered
   verbatim (freeze, cut checks, the probe's `example`).
5. **Hosts first** (`policy.md` §1): is H2-F the right host boundary? Is its contract generic in
   what its consumers vary: U₀ at `k = 1`, U2-U at `k = 2`, U2-E through the ruler host, and U-1?
6. **Debt.** Verify the duplication ledger.

Attempt at least three adversarial instantiations: `k = 0`; a scheme whose decoding is constant;
a table whose machine halts at once, so `t = 1`. Propose any missing sanity theorems.

## Open questions for this gate (maintainer recommendations in italics)

1. **H2-F's home.**
   - `Build/StepBlockLoop.lean`, as briefed, puts `CodeSimulator` and its downstream in the
     replay: 10 modules, including `CodeSimulator`, whose B5a continuation is next.
   - A new `Build/StepBlockForward.lean` (importing `StepBlock` and `Contract/Basic`) would keep
     the replay to 5 modules and leave `CodeSimulator` unrebuilt.
   - *Keep `StepBlockLoop` (both loop forms in one module, as briefed). Land after the B5a
     continuation's merge window to avoid a concurrent rebuild.*
2. **The duplication ledger's two items.** *Acknowledge both; no payback.*
3. **Field name `machine`** (versus `decode`, which on the received schemes returns a code
   rather than a machine). *Keep `machine`.*
4. **`exists_code2TM`** (end of the chain). It needs a home and a dedup decision: a mirror of
   `Encoding.exists_codeTM_spaceUsed` in `Codes2Tape`, or a `k`-generic relabelling lemma in
   `StateRenaming` with both as corollaries. *The generic lemma, at the end of the chain, after
   MIG-1 stage S (which touches `Encoding`).*
5. **U2-E's fill timing.** *After B6's ruler-host fill; U2-E's statement is gated now so U-1 can
   be planned.*

## Size estimates (ESTIMATE, lines landed; MEASURED where marked)

| Item | Lines |
|---|---|
| This unit (MEASURED) | `UniversalK` 279 (new); `StepBlockLoop` 511 → 595; `SelfUniversal` 154 → 161 (50 lines in, 43 out); `Codes2Tape` 330 → 336; facade 225 → 232 |
| H2-F fill (`exists_forwardLoopTM`) | 600–1,100 |
| U2-S fill (`exists_selfStartupTMK`) | 500–1,000 |
| U2-U fill (`exists_selfUniversalK`) | 250–500 |
| U2-E fill (`universalK`) | 500–1,000, after B6's ruler host |
| **Total fill** | **about 1.9k–3.6k**; B6's `U₀` fill folds into it |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: as in `audits/TEMPLATE.md`.

## Appendix: the statements as landed (generated by `scripts/appendix.py`)

### `TCSlib/Complexity/TuringMachine/UniversalK.lean`

#### `Turing.EffectiveCodeK` (structure, new, line 87)

```lean
/-- **An effective scheme for `k`-work-tape codes** [AB09, §1.4]: a total decoding of every
string `α` into a `k`-work-tape binary machine `machine α` with state space
`Fin (numStates α + 1)`, together with a machine of this development, the canonizer, that
computes from `α` the fixed `k`-record serialization `Turing.serializeK (machine α)` within an
arbitrary time bound `canonizerTime`. As for `Turing.EffectiveMachineCode` (Argument A), the
canonizer targets the fixed, scheme-independent serialization, and its time bound is arbitrary:
fixed-code consumers absorb it into their constants. The received schemes are instances
(`Turing.EffectiveMachineCode.toK`, `Turing.EffectiveMachineCode2.toK`). -/
structure EffectiveCodeK (k : ℕ) where
  /-- one less than the number of states of the machine a string denotes -/
  numStates : List Bool → ℕ
  /-- the machine a string denotes -/
  machine : (α : List Bool) → MultiTapeTM k Bool (Fin (numStates α + 1))
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's (arbitrary) time bound -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serializeK ∘ machine` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => serializeK (machine α)) canonizerTime
```

#### `Turing.EffectiveCodeK.toFinTM` (def, new, line 102)

```lean
/-- The bundled machine a string denotes in a `k`-tape scheme: `k` work tapes, the states
`Fin (numStates α + 1)`, the decoded machine. -/
def EffectiveCodeK.toFinTM {k : ℕ} (E : EffectiveCodeK k) (α : List Bool) : FinTM Bool where
  k := k
  State := Fin (E.numStates α + 1)
  tm := E.machine α
```

#### `Turing.EffectiveCodeK.ofSerialize` (def, new, line 112)

```lean
/-- **A `k`-tape scheme from a scheme with its own serialization** (the common constructor of
the two instances below): given a type of coded machines with their state counts and their
`k`-tape machines, a serialization equal to `serializeK` of the machine, a decoding, and a
canonizer computing the serialization of the decoded machine, the `k`-tape scheme with the same
decoding and canonizer. -/
def EffectiveCodeK.ofSerialize {k : ℕ} {Code : Type} (numStates : Code → ℕ)
    (tm : (M : Code) → MultiTapeTM k Bool (Fin (numStates M + 1))) (serialize : Code → List Bool)
    (serialize_eq : ∀ M, serialize M = serializeK (tm M)) (decode : List Bool → Code)
    (canonizer : FinTM Bool) (canonizerTime : ℕ → ℕ)
    (h : canonizer.ComputesFunInTime (fun α => serialize (decode α)) canonizerTime) :
    EffectiveCodeK k where
  numStates α := numStates (decode α)
  machine α := tm (decode α)
  canonizer := canonizer
  canonizerTime := canonizerTime
  canonizer_computes := by
    have e : (fun α => serialize (decode α)) = fun α => serializeK (tm (decode α)) :=
      funext fun α => serialize_eq (decode α)
    exact e ▸ h
```

#### `Turing.EffectiveMachineCode.toK` (def, new, line 130)

```lean
/-- **The received one-tape scheme as a `k`-tape scheme** (`k = 1`): the same decoding and the
same canonizer, whose target `CodeTM.serialize` is `serializeK` at one work tape
(`Turing.oneTapeMachineFormat.serialize_eq`). [AB09, §1.4] -/
def EffectiveMachineCode.toK (c : EffectiveMachineCode) : EffectiveCodeK 1 :=
  EffectiveCodeK.ofSerialize CodeTM.numStates CodeTM.tm CodeTM.serialize
    oneTapeMachineFormat.serialize_eq c.decode c.canonizer c.canonizerTime c.canonizer_computes
```

#### `Turing.EffectiveMachineCode2.toK` (def, new, line 137)

```lean
/-- **The Z3 two-tape scheme as a `k`-tape scheme** (`k = 2`): the same decoding and the same
canonizer, whose target `Code2TM.serialize` is `serializeK` at two work tapes
(`Turing.Code2TM.serialize_eq_serializeK`). [AB09, §1.4] -/
def EffectiveMachineCode2.toK (c : EffectiveMachineCode2) : EffectiveCodeK 2 :=
  EffectiveCodeK.ofSerialize Code2TM.numStates Code2TM.tm Code2TM.serialize
    Code2TM.serialize_eq_serializeK c.decode c.canonizer c.canonizerTime c.canonizer_computes
```

#### `Turing.EffectiveMachineCode.toK_toFinTM` (theorem, new, line 142)

```lean
/-- The one-tape scheme's `k`-tape view denotes the same bundled machines, by definition. -/
theorem EffectiveMachineCode.toK_toFinTM (c : EffectiveMachineCode) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := …
```

#### `Turing.EffectiveMachineCode2.toK_toFinTM` (theorem, new, line 146)

```lean
/-- The two-tape scheme's `k`-tape view denotes the same bundled machines, by definition. -/
theorem EffectiveMachineCode2.toK_toFinTM (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.toFinTM α = (c.decode α).toFinTM := …
```

#### `Turing.EffectiveMachineCode.toK_machine` (theorem, new, line 150)

```lean
/-- The one-tape scheme's `k`-tape view decodes to the same machines, by definition. -/
theorem EffectiveMachineCode.toK_machine (c : EffectiveMachineCode) (α : List Bool) :
    c.toK.machine α = (c.decode α).tm := …
```

#### `Turing.EffectiveMachineCode2.toK_machine` (theorem, new, line 154)

```lean
/-- The two-tape scheme's `k`-tape view decodes to the same machines, by definition. -/
theorem EffectiveMachineCode2.toK_machine (c : EffectiveMachineCode2) (α : List Bool) :
    c.toK.machine α = (c.decode α).tm := …
```

#### `Turing.exists_selfStartupTMK` (theorem, new, line 188)

```lean
/-- **U2-S, the `k`-generic startup** (the startup of `Turing.exists_selfStartupTM`, generic in
the work-tape count). For a `k`-tape scheme `E` there is a binary machine with `K + (k + 2)` work
tapes and an exit state such that for every code `α` there are a time `T` and a space bound `B`,
**depending on `α` only**, with the following property on every input `pairEncode α w`. At time
`T`, and not earlier, it is at its exit with:
* the input head at position `1`, `Cfg.init`'s position, and the output empty, having emitted
  nothing before;
* tapes `0, …, k - 1`, the simulated work tapes, blank, and tape `k` holding the canonical table
  `Turing.tableBitsK` of the decoded machine;
* tape `k + 1` holding the decoded machine's initial state in unary from cell `2` (cells `0`
  and `1` blank), the step block's summary tape for an empty output;
* every other tape blank and every head at `0`.

Up to `T` it has visited at most `B` cells. This configuration is the step block's seam
(`Turing.StepBlock.Rep`) for the decoded machine's initial configuration on the same input, and
its restriction to the first `k + 2` tapes is H2-F's encoding `Turing.StepBlock.forwardLoopCfg` of
that configuration. [AB09, §1.4.1, Theorem 1.9]

**Proof sketch.** As `Turing.exists_selfStartupTM`'s, at `k` mirrored tapes. Extract and
canonize: the prefix parser composed with the scheme's canonizer by buffered composition, its
emissions captured on a scratch tape (the pattern of `Turing.universalCanonTM` and
`Turing.universalCaptureTM`, with `E.canonizer` in place of the one-tape scheme's); it ends after
`3|α| + 4 + E.canonizerTime |α|` steps with `serializeK (E.machine α)` captured and the input
head at `2|α| + 3`. Skip the doubled state count and the separator of
`serializeK = pairEncode n.bits (unaryFin q₀ ++ tableBitsK tr)`, copy the unary initial state to
tape `k + 1` at offset `2` and the table to tape `k`; clear the scratch and the buffer. Rewind the
input head to position `1` (`Turing.FinTM.timed_rewind`, `2|α| + 5` steps). Every phase depends
on `α` only, so `T` and `B` do (`Turing.MultiTapeTM.spaceUsed_le_mul_succ` at the canonizer's
halting time bounds its cells). -/
theorem exists_selfStartupTMK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + (k + 2)) Bool P) (exit : P),
      ∀ α : List Bool, ∃ T B : ℕ, ∀ w : List Bool,
        R.runFrom (R.initCfg (pairEncode α w)) T =
          ⟨some exit, 1,
            fun j => if j.val = k then FinTM.bufferTape (tableBitsK (E.machine α).tr)
              else if j.val = k + 1 then
                fun p => FinTM.bufferTape (unaryFin (E.machine α).q₀) (p - 2)
              else fun _ => none,
            fun _ => 0, []⟩ ∧
        (∀ u < T, (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some exit) ∧
        (∀ u ≤ T, (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
        R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by
  sorry
```

#### `Turing.exists_selfUniversalK` (theorem, new, line 233)

```lean
/-- **U2-U, the self-application universal machine, with time and space ledgers and the
converse** [AB09, Theorem 1.9 and Exercise 4.1, at self-application]. For a `k`-tape scheme `E`
there is a binary machine `U` such that for every code `α` there is a constant `C > 0`
(depending on `α` only) with, for every `w`:
* whenever the machine coded by `α` halts on `pairEncode α w` with `output` within `t` steps,
  `U` halts on the same input with the same `output` within `C · (t + 1)` steps, having visited
  by then at most `C · (s + 1)` cells, `s` the coded machine's cells by time `t`;
* every completed output of `U` on `pairEncode α w` is a completed output of the coded machine
  there (so divergence is preserved).

`C` depends on the code string, as in `Turing.universal` (Argument E): it absorbs the canonizer's
arbitrary time and the table's length. B6's `Turing.exists_selfUniversal` is the case `k = 1`
(forward clause, space only).

**Proof sketch.** Startup, then H2-F. (i) U2-S reaches, after `T_α` steps and within `B_α`
cells, H2-F's encoding `Turing.StepBlock.forwardLoopCfg entry M (M.initCfg (pairEncode α w))` of
the coded machine `M := E.machine α`, on the block's tapes, the other tapes blank; seam it into
H2-F's machine `L` (R2, R1 on the first `k + 2` tapes). (ii) H2-F's lockstep
(`Turing.Lockstep.runFrom`) runs `M` from its initial configuration: after `M` halts at `t`,
`L` is at the encoding of the halted configuration, halted, with `M`'s output, after
`Σ_{u < t} cost ≤ (50 · (|tableBitsK| + 1) + C_L) · t` steps; so the time is at most
`T_α + (50 · (|tableBitsK| + 1) + C_L) · t ≤ C · (t + 1)`. (iii) Space: the mirrored heads visit
only `M`'s cells, at most `s`; the auxiliary heads stay in an interval of length
`2 (50 · (|tableBitsK| + 1) + C_L) + 1`; the startup `B_α`; in all `≤ C · (s + 1)`, and the
halted configuration is frozen afterwards. (iv) Converse: by the lockstep's cut
(`Turing.Lockstep.cut`) `L` is live while `M` is, and an encoded live configuration is live, so
`U` halts only at the encoding of a halted configuration of `M`, whose output is `M`'s. -/
theorem exists_selfUniversalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧ ∀ w : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (E.toFinTM α).ComputesInTime (pairEncode α w) output t →
        U.ComputesInTime (pairEncode α w) output (C * (t + 1)) ∧
        U.tm.spaceUsed (U.tm.initCfg (pairEncode α w)) (C * (t + 1)) ≤
          C * ((E.toFinTM α).tm.spaceUsed ((E.toFinTM α).tm.initCfg (pairEncode α w)) t + 1)) ∧
      ∀ output : List Bool, (∃ t', U.ComputesInTime (pairEncode α w) output t') →
        ∃ t, (E.toFinTM α).ComputesInTime (pairEncode α w) output t := by
  sorry
```

#### `Turing.universalK` (theorem, new, line 271)

```lean
/-- **U2-E, the code-first evaluator** [AB09, Theorem 1.9, the evaluator `U(x, α) = M_α(x)`, in
the code-first layout of `Turing.universal`]. For a `k`-tape scheme `E` there is a binary
machine `U` such that for every code `α` there is a constant `C` (depending on `α` only) with,
for every input `x`:
* whenever the machine coded by `α` halts on `x` with `output` within `t` steps, `U` halts on
  `pairEncode α x` with the same `output` within `C · (t + 1)` steps (no term in `|x|`);
* every completed output of `U` on `pairEncode α x` is a completed output of the coded machine
  on `x`.

At `k = 1` and `E := c.toK` this is `Turing.universal c`'s statement (shown in the gate's
probe); re-deriving `Turing.universal` from it is the U-1 retrofit, deferred until this
statement is filled. At `k = 2` it is the core of Theorem 1.9 at `T log T` with the
Hennie–Stearns conversion (design note §4).

**Proof sketch.** (i) *Code-first startup:* scan the doubled code and its separator, writing
one ruler cell per header cell, so the ruler is `true^ℓ` with `ℓ = 2|α| + 2`, the header length
(`Turing.universal_pair_length`); extract and canonize `α` as U2-S does, installing H2-F's
encoding of `M := E.machine α`'s initial configuration on the virtual input `x` (virtual
position `1`, physical head at `ℓ + 1`). (ii) *Ruler host:* run H2-F's machine `L` through H5's
bounded-prefix ruler host (`Turing.exists_rulerHostTM`, `Turing.RulerAt`): a block simulation
of `L` on the suffix input `x`, with at most `C_R · (ℓ + 1)` host steps per step of `L`, the same
bank and output, and exit cut. Composing with H2-F's lockstep, each step of `M` costs at most
`C_R (ℓ + 1)(50 · (|tableBitsK| + 1) + C_L)`, a constant for fixed `α`; with the startup this is
`≤ C · (t + 1)`. (iii) *Converse:* the ruler host does not halt before `L`, nor `L` before `M`
(the two cuts), so every completed output of `U` is `M`'s on `x`. -/
theorem universalK (k : ℕ) (E : EffectiveCodeK k) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ), (E.toFinTM α).ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      ∀ output : List Bool, (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (E.toFinTM α).ComputesInTime x output t := by
  sorry
```

### `TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean`

#### `Turing.StepBlock.forwardLoopCfg` (def, new, line 529)

```lean
/-- **The forwarding round loop's configuration for a source configuration** (H2-F's encoding):
for a `k`-work-tape binary machine `M` with `n + 1` states and a configuration `c` of `M` on the
input `x`, the `(k + 2)`-tape configuration whose input head and mirrored tapes `0, …, k - 1`
(contents and heads) are `c`'s, whose tape `k` holds the table `tableBitsK M.tr` and tape
`k + 1` the blank summary cell followed by the unary current state (empty when `c` is halted),
both auxiliary heads at `0`, whose output is `c`'s output, and whose control is `entry` while
`c` is live and halted once `c` is. It is the step block's seam relation `Turing.StepBlock.Rep`
for `c` with its output erased (so the summary cell is blank), with the physical output
restored: the reset invariant of `Turing.exists_selfUniversal`'s sketch (the H2-S gate's
finding 4). [AB09, §1.4.1, proof of Theorem 1.9] -/
def forwardLoopCfg {k n : ℕ} {Q : Type} {x : List Bool} (entry : Q)
    (M : MultiTapeTM k Bool (Fin (n + 1))) (c : Cfg k Bool (Fin (n + 1)) x) :
    Cfg (k + 2) Bool Q x where
  state := c.state.map fun _ => entry
  inputPos := c.inputPos
  workTapes := Fin.addCases (motive := fun _ => ℤ → Option Bool) c.workTapes fun j =>
    if j = 0 then FinTM.bufferTape (tableBitsK M.tr)
    else summaryCells none ((c.state.map unaryFin).getD [])
  workTapePos := Fin.addCases (motive := fun _ => ℤ) c.workTapePos fun _ => 0
  output := c.output
```

#### `Turing.StepBlock.exists_forwardLoopTM` (theorem, new, line 574)

```lean
/-- **H2-F, the forwarding round loop** (host H2's unclocked loop form; `machine-library-design.md`
§14; U2 design note `audits/evidence/u2/U2-design.md` §2.2). For each work-tape count `k` there
is one finite `(k + 2)`-tape binary machine `L`, with an entry state and a constant `C`, such
that for every `k`-work-tape binary machine `M` with `n + 1` states and every input `x`, `L`
simulates `M` step by step through `forwardLoopCfg`: there is a cost function on `M`'s
configurations with
* **a macro-step lockstep** (`Turing.Lockstep`, exits `{none}` on both sides): from the encoding
  of a live configuration `c`, `L` reaches the encoding of `M.step c` after exactly `cost c`
  steps, without halting before; the encoding of a halted configuration is halted. So `L` halts
  exactly when `M` does, with `M`'s output, which it emits step by step
  (`Turing.Lockstep.runFrom`, `Turing.Lockstep.cut`);
* **a per-step bound**: `0 < cost c ≤ 50 · (|tableBitsK M.tr| + 1) + C` for live `c`, a constant
  for a fixed table (the step block's bound plus the leaf's);
* **a space ledger**: over `t` source steps that are live before `t`, each mirrored head visits
  only cells that `M`'s head visits, and the two auxiliary heads stay within
  `50 · (|tableBitsK M.tr| + 1) + C` of their home.

The control of `L` does not depend on `M`, `n` or `x`. [AB09, §1.4.1, proof of Theorem 1.9:
each step of `M` is simulated in a number of steps depending only on `M`'s table]

**Proof sketch.** `L` is the step block `roundTM k` followed, at either of its exits, by a
forwarding leaf on the summary tape: read the summary cell, emit its bit if it holds one, blank
it, then return to the block's entry (exit `entry`) or halt (exit `halt`). For a live `c`, the
block-control part of `forwardLoopCfg entry M c` represents `{c with output := []}` (`Rep`: a blank
summary, the unary state word, both auxiliary heads home), so `roundTM_effect` gives a first exit
after `T ≤ 50 · (|tableBitsK M.tr| + 1)` steps at the representation of
`a.apply {c with output := []}`, silent before, with summary cell
`summaryEmit none a.output = a.output` (`summaryEmit_none`); the exit time is unique
(`roundTM_firstExit_unique`). The leaf emits `a.output`, making the physical output
`(a.apply c).output`, blanks the cell, and enters `entry` or halts according to the exit: the
result is exactly `forwardLoopCfg entry M (M.step c)`. Take `cost c` the block's exit time plus the
leaf's length (at most `C`); the inner times are live by the block's cut and the leaf's. The space
ledger is `roundTM_visited` per round, summed by `MultiTapeTM.visitedByTapeHead_add_subset`; the
leaf moves no head. -/
theorem exists_forwardLoopTM (k : ℕ) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (L : MultiTapeTM (k + 2) Bool Q)
      (entry : Q) (C : ℕ),
      ∀ {n : ℕ} {x : List Bool} (M : MultiTapeTM k Bool (Fin (n + 1))),
        ∃ cost : Cfg k Bool (Fin (n + 1)) x → ℕ,
          Lockstep M L (forwardLoopCfg entry M) cost {none} {none} ∧
          (∀ c, c.state ≠ none → 0 < cost c ∧
            cost c ≤ 50 * ((tableBitsK M.tr).length + 1) + C) ∧
          ∀ (c : Cfg k Bool (Fin (n + 1)) x) (t : ℕ), (∀ u < t, (M.runFrom c u).state ≠ none) →
            (∀ i : Fin k, L.visitedByTapeHead (forwardLoopCfg entry M c)
                (∑ u ∈ Finset.range t, cost (M.runFrom c u)) (Fin.castAdd 2 i) ⊆
              M.visitedByTapeHead c t i) ∧
            ∀ j : Fin (k + 2), k ≤ j.val →
              L.visitedByTapeHead (forwardLoopCfg entry M c)
                  (∑ u ∈ Finset.range t, cost (M.runFrom c u)) j ⊆
                Finset.Icc (-((50 * ((tableBitsK M.tr).length + 1) + C : ℕ) : ℤ))
                  ((50 * ((tableBitsK M.tr).length + 1) + C : ℕ) : ℤ) := by
  sorry
```

### `TCSlib/Complexity/TuringMachine/SelfUniversal.lean`

#### `Turing.exists_selfStartupTM` (theorem, received, body changed, line 89)

```lean
/-- **`U₀`'s startup** (the RD-3 gate's check 2). For an effective scheme `c` there is a binary
machine with `K + 3` work tapes and an exit state such that for every code `α` there are a
time `T` and a space bound `B`, **depending on `α` only**, with the following property on every
input `pairEncode α w`. At time `T`, and not earlier, it is at its exit with:
* the input head at position `1`, `Cfg.init`'s position, and the output empty, having emitted
  nothing before (administrative output suppressed);
* tape `0`, the simulated work tape, blank, and tape `1` holding the canonical table
  `Turing.tableBitsK` of the decoded machine;
* tape `2` holding the decoded machine's initial state in unary from cell `2` (cells `0` and
  `1` blank), which is the step block's summary tape for an empty output;
* every other tape blank and every head at `0`.

Up to `T` it has visited at most `B` cells. This configuration is the step block's seam for
the decoded machine's initial configuration on the same input (H2's seam relation
`Turing.StepBlock.Rep`, `TuringMachine/Build/StepBlock.lean`, at one coded work tape). [AB09,
§1.4.1, Theorem 1.9]

**Proof sketch.** The case `k = 1`, `E := c.toK` of `Turing.exists_selfStartupTMK`, whose
sketch is this construction at `k` mirrored tapes (extract and canonize, install the table and
the unary state, rewind the input head). The generic tape indices `k` and `k + 1` are `1` and
`2`, and `c.toK` decodes to the same machines (`Turing.EffectiveMachineCode.toK_toFinTM`). -/
theorem exists_selfStartupTM (c : EffectiveMachineCode) :
    ∃ (K : ℕ) (P : Type) (_ : Fintype P) (_ : DecidableEq P)
      (R : MultiTapeTM (K + 3) Bool P) (exit : P),
      ∀ α : List Bool, ∃ T B : ℕ, ∀ w : List Bool,
        R.runFrom (R.initCfg (pairEncode α w)) T =
          ⟨some exit, 1,
            fun j => if j = 1 then FinTM.bufferTape (tableBitsK (c.decode α).tm.tr)
              else if j = 2 then fun p => FinTM.bufferTape (unaryFin (c.decode α).tm.q₀) (p - 2)
              else fun _ => none,
            fun _ => 0, []⟩ ∧
        (∀ u < T, (R.runFrom (R.initCfg (pairEncode α w)) u).state ≠ some exit) ∧
        (∀ u ≤ T, (R.runFrom (R.initCfg (pairEncode α w)) u).output = []) ∧
        R.spaceUsed (R.initCfg (pairEncode α w)) T ≤ B := by
  obtain ⟨K, P, hP, dP, R, exit, h⟩ := exists_selfStartupTMK 1 c.toK
  refine ⟨K, P, hP, dP, R, exit, fun α => ?_⟩
  obtain ⟨T, B, hT⟩ := h α
  refine ⟨T, B, fun w => ?_⟩
  obtain ⟨hrun, hcut, hout, hspace⟩ := hT w
  refine ⟨?_, hcut, hout, hspace⟩
  rw [hrun]
  congr 1
  funext j
  have m1 : 1 % (K + 3) = 1 := Nat.mod_eq_of_lt (by omega)
  have m2 : 2 % (K + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  have h1 : (j = 1) ↔ j.val = 1 := by
    rw [Fin.ext_iff]; simp [m1]
  have h2 : (j = 2) ↔ j.val = 2 := by
    rw [Fin.ext_iff]; simp [m2]
  by_cases a : j.val = 1
  · simp [h1.mpr a, EffectiveMachineCode.toK_machine]
  · by_cases b : j.val = 2
    · have hne : (2 : Fin (K + (1 + 2))) ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp [m1, m2] at this
      simp [h2.mpr b, hne, m2, EffectiveMachineCode.toK_machine]
    · simp [a, b, h1, h2]
```

#### `Turing.exists_selfUniversal` (theorem, received, body changed, line 145)

```lean
/-- **`U₀`, the self-application universal machine** (`Complexity.space_hierarchy`'s sketch;
the sibling of `Complexity.space_universal`, with the native device in place of the
bounded-prefix one). For an effective scheme `c` there is a binary machine `U₀` such that
for every code `α` there is a constant `C > 0` with: whenever the machine coded by `α` halts
on `pairEncode α w` with some output, having visited at most `s` cells, `U₀` halts on the same
input with the same output, having visited at most `C · (s + 1)` cells. Only this forward
direction is claimed; `Complexity.space_hierarchy` instantiates
`c := Complexity.TimeHierarchy.code`. [AB09, Exercise 4.1, forward clause, at self-application;
§4.1.3, Theorem 4.8]

Deviation: `C` depends on the code `α` (as in `Turing.universal`), and the input is the coded
machine's own input (self-application), so no copy and no position counter is needed.

**Proof sketch.** The case `k = 1`, `E := c.toK` of `Turing.exists_selfUniversalK`, whose
sketch is this construction at `k` mirrored tapes (the startup, then H2-F's forwarding round loop
`Turing.StepBlock.exists_forwardLoopTM`, the wrapped rounds with the reset invariant, made a public
host). Its forward clause gives the halting run within `C · (t + 1)` steps, so `t' := C · (t + 1)`,
and the space `≤ C · (spaceUsed + 1) ≤ C · (s + 1)`; its time clause and converse are dropped. -/
theorem exists_selfUniversal (c : EffectiveMachineCode) :
    ∃ U₀ : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (w output : List Bool) (t s : ℕ),
        (c.decode α).toFinTM.ComputesInTime (pairEncode α w) output t →
        (c.decode α).toFinTM.tm.spaceUsed
            ((c.decode α).toFinTM.tm.initCfg (pairEncode α w)) t ≤ s →
          ∃ t' : ℕ, U₀.ComputesInTime (pairEncode α w) output t' ∧
            U₀.tm.spaceUsed (U₀.tm.initCfg (pairEncode α w)) t' ≤ C * (s + 1) := by
  obtain ⟨U, hU⟩ := exists_selfUniversalK 1 c.toK
  refine ⟨U, fun α => ?_⟩
  obtain ⟨C, hC, h⟩ := hU α
  refine ⟨C, hC, fun w output t s hrun hs => ⟨C * (t + 1), ((h w).1 output t hrun).1, ?_⟩⟩
  have hsp := ((h w).1 output t hrun).2
  rw [EffectiveMachineCode.toK_toFinTM] at hsp
  exact hsp.trans (Nat.mul_le_mul_left C (by omega))
```

### `TCSlib/Complexity/TuringMachine/Codes2Tape.lean`

#### `Turing.Code2TM.serialize_eq_serializeK` (lemma, promoted, line 291)

```lean
/-- **The two-tape serialization is the generic one** [AB09, §1.4]: for every coded two-tape
machine `M`, the frozen serialization `M.serialize` is the fixed `k`-record serialization
`serializeK M.tm` at two work tapes. (Promoted from the private `twoTape_serialize_eq` for the
two-tape scheme's `k`-tape view `Turing.EffectiveMachineCode2.toK`; statement and proof
unchanged.) -/
lemma Code2TM.serialize_eq_serializeK (M : Code2TM) : M.serialize = serializeK M.tm := by
  unfold Code2TM.serialize serializeK
  rw [tableBitsK_two]
  simp only [codeTable2Bits, actionBits₂_eq_actionBitsK]
```

#### `Turing.twoTapeMachineFormat` (def, received, body changed, line 297)

```lean
/-- The existing two-tape parser equipped with its fixed machine semantics. -/
private def twoTapeMachineFormat : MachineFormat :=
  MachineFormat.mk twoTapeFormat 2 Code2TM.tm
    Code2TM.serialize_eq_serializeK codeSkipTable2_eq_codeSkipTableK
```

