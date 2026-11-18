# Gate 162 · RAM tier 2: the statements (PR #372)

**A statement gate** (design note `items/ram-tm/TIER2-DESIGN.md`, decision D5; Seyoon,
2026-11-18). PR #372 is a draft into `complexity/ram-simulation`. It adds the public statements
that five fill jobs, A–E, will prove in parallel, and the internal interfaces of the simulation.
Together they prove the two frozen targets `WordRAM.exists_simulation` and
`WordRAM.exists_ndSimulation`. No fill starts before this gate clears. Seyoon dispatches and
merges.

- **Lean head:** `e1325c96cf035f0ed6710443d89c3fcb6026a5c4` (branch `ram/tier2-statements`): one
  commit on the RAM branch's Lean `adb694d2` (#371 merged).
- **Approvals** (Seyoon, 2026-11-18): D1–D5 of the design note:
  - the new public `Build/` modules;
  - the simulation split under `RAMSimulation/Sim/` with public lemmas in the internal namespace
    `WordRAM.Sim`;
  - reuse of `RecordTable`'s layout;
  - one induction for both forms;
  - this audit.

  Also two edits to frozen files: readers in `Programs/WordRAM/Extended.lean`, and two imports in
  `RAMSimulation/Simulation.lean`.

## What it adds

| Module | Content | Proved? | Job |
|---|---|---|---|
| `Build/Contract/Reach` | `Turing.ReachesWithin` (endpoint within `B` steps, no exit earlier, heads within radius `E`); `ReachesWithin.mono`; `Turing.Contract.ofReaches`, the contract of such a row, with `ofReaches_time_le` | **all proved** | — |
| `Build/WordArith` | `bvBits`, `WordAt`, `wordWrite`, `ScratchBlank`, with readers (proved); `bvBits_injective` and nine five-tape rows: add, sub, mul, half, sign extension, integer constant, sign test, zero test (sorried) | readers yes | A |
| `Build/KeyTable` | `keyFields`, `keyTableLength`, `KeyTableAt`, `keyTableWrite`, `keyLookup`, `keyAssign`, with readers (proved); `exists_keyLookupTM`, `exists_keyAssignTM` (sorried) | readers yes | B |
| `Build/InputBit` | `exists_inputBitTM` (sorried) | — | C |
| `RAMSimulation/Sim/Encoding` | `keyBits`, `immediates`, `ImmBound`, `TableOf`, `Encodes`, with readers | **all proved** | — |
| `RAMSimulation/Sim/Startup` | `exists_startup` (sorried) | — | C |
| `RAMSimulation/Sim/Phases` | `isCoin`, `isVerdict`, `jumpTarget`, with readers (proved); `exists_phase`, `exists_verdictPhase` (sorried) | readers yes | D |
| `Programs/WordRAM/Extended` | 12 readers (`inBitWord_def`, `coinWord_def`, `xstep_def`, `XSteps.zero_iff`/`succ_iff`, `baseTouches_def`, `XInstr.touches_def`, `XStepsIn.zero_iff`/`succ_iff`, `initMem_def`, `XCfg.init_def`, `haltsWithin_iff`), each `rfl` | **all proved** | — |
| `RAMSimulation/Simulation` | imports `Sim/Startup` and `Sim/Phases`; the two targets unchanged | — | E |
| facades | `Build/Contract`, `TuringMachine`, `RAMSimulation`: imports and contents lines | — | — |

Job E proves the two targets from `exists_startup`, `exists_phase` and `exists_verdictPhase`, in
files of its own under `RAMSimulation/Sim/`.

### The design, in brief

- **Words** of `W` bits are held least significant first, delimited by blanks (`WordAt`). Every
  row of `Build/WordArith` is a five-tape machine: operands on tapes `0` and `1`, the
  destination on `2`, blank scratch on `3` and `4`. It writes only the destination's word
  interval and returns every head. Words keep one width, so an operand's own delimiters bound
  each scan and `W = 0` needs no case. The design note's unary ruler is therefore dropped (a
  deviation from the note's §3, recorded here).
- **The memory** is a keyed table (`Build/KeyTable`) in `RecordTable`'s layout (D2), under the
  header `[true]`. Each entry is the two fields `true :: key` and `true :: value`; the marker
  keeps every field nonempty, so the layout is well formed even for `W = 0`. The rows look up
  and assign by a key held on another tape. They do not use the admitted
  `exists_tableFindTM` and `exists_tableAppendTM`, which select by a finite-state predicate.
- **Keys** are `W + a` bits of two's complement (`keyBits`). A computed address is a word's
  signed value, in range for `W` bits. An immediate is in range for `a` bits (`ImmBound`). In the
  range of `W + a` bits, distinct cells have distinct keys.
- **`Encodes`:** eight tapes (table, key register, three word registers, `Nat.bits |x|`, two
  scratch tapes), heads at fixed origins, output `c.out` in function mode and empty in verdict
  mode. `TableOf` ties the table to the memory over a cell set `T`: distinct keys; each entry is
  a cell of `T` in range with its word; every nonzero cell in range has an entry. So the table
  has at most `|T|` entries.
- **Phases** are nondeterministic machines whose transitions differ only at a `coin` phase's
  entry, and that entry is never re-entered. Each is stated for each fixed choice `b`. The
  deterministic simulation fixes `false`, which matches the stream `ρ = []`.

### How the interfaces give the frozen bounds (job E's argument)

Let `n = |x|`. Take `t`, `f`, `K` from `HaltsWithin` (`s < t` non-verdict steps, `|K| ≤ f`), and
`T_i = {-1} ∪` the cells touched in the first `i` steps. Then `T_i ⊆ {-1} ∪ K`, so
`|T_i| ≤ f + 1`.

- **Time.**
  - The start-up takes at most `tw + C₀·(n + W² + 1)` steps, with `tw ≤ TW n`.
  - Each of the `s < t` phases takes at most `C₁·((f + 2)·(W + 1) + W² + n + 1)` steps, plus one
    dispatch step of the phase host.
  - The verdict phase takes at most `C₂` steps, plus its dispatch.
  - Since `(f + 2)·(W + 1) ≤ 2·(f·(W + 1) + W² + n + 1)` and `t ≥ 1`, the sum is at most
    `TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)` for a constant `A`.
- **Space.**
  - The start-up visits at most `sw + C₀·(W + |bits n| + 1)` cells, with `sw ≤ SW n`.
  - After it, each of the eight tapes stays within its origin `± C₁·((f + 2)·(W + 1) + |bits n| + 1)`.
    The phases' radius is relative to their start, and every phase starts at the origins.
  - The extra tapes never move after the start-up (they are outside the embedded phases).
  - Since `|bits n| ≤ logSpace n`, the total is at most `SW n + A·(f·(W + 1) + W + logSpace n + 1)`.
- **The nondeterministic form.**
  - A branch with choice word `w` runs the stream of `w`'s bits at the coin phases' entries. The
    phases agree elsewhere, so `Turing.NDTM.runWith_eq_fixChoice_runFrom` applies slice by slice.
  - The uniform hypothesis bounds every branch.
  - Acceptance matches by `HaltsWithin.unique`.

## Brief for the auditor

1. **Truth.** Check that every sorried statement is true and provable as stated, at the
   boundaries too: `W = 0`, `n = 0`, `a = 0` where allowed, empty keys and tables, `c` negative,
   an input position off the input or negative, and `bltz` to its own position. Check the bounds:
   that each time and radius bound is achievable by the sketched machine.
2. **Sufficiency.** Check that the statements suffice for the two frozen targets, by the argument
   above: the bounds, the dispatch, the embedding of the eight tapes among the start-up's, and the
   nondeterministic slicing (`exists_phase`'s agreement and no-re-entry clauses). Report any
   missing clause that job E would need.
3. **The encoding.** Check `keyBits`, `ImmBound`, `TableOf` and `Encodes`. Lookups must be
   correct for every address a step reads, and the table must stay within `|T|` entries.
4. **Readers and the freeze.** Check that the 12 `Extended` readers restate their definitions
   exactly and that no existing statement changed (`SOURCE.json`: 69 declarations added, no
   header or definition change).
5. **Library fit.** Check the homes (D1, D2). Check that the rows do not duplicate published
   ones (`copyTM`, `compareTM`, `scanTM`, the `RecordTable` rows, `exists_inputSeekTM`). Check the
   docstrings and proof sketches, and the proved parts (`Contract.ofReaches`).

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay of the 12 owners' downstream closure on
  `oleans-cl161-cl160`, the branch's build after #371. 88 modules: 88 passed, 0 failed.
  - 30 admissions in the replayed sources: this PR's 15 statements (WordArith 9, KeyTable 2,
    InputBit 1, Startup 1, Phases 2), and 15 inherited: RecordTable 4 (not used here),
    Simulation 2 (the targets) and Classes 9 (proved by #373, gate 163; the two PRs share no
    file).
  - Pool 3; 547 s.
- **`SOURCE.json`:** 12 owners, 69 declarations added; none removed; no header or definition
  change to an existing declaration.
- **Seals:** the 49 changed or added proofs pass with every foreign definition they reach sealed
  (24 heads). They include the proved adapter, readers and definitions, and the statements'
  types.
- **Controls:** 32 definitions and 64 identities, each native-PASS and sealed-FAIL.
- **The metadata check** admits `sorryAx` only for the 15 statements named in `gate.json`
  (`inherited_admissions`), which are this PR's sorried statements. This allowance is the kit
  change made at gate 163.
- **Sweeps:** the proof-syntax sweep finds 49 roots and 0 read candidates. Citation homes are in
  `CITATION-HOMES.json`.
- **Copy screen** (population: the 12 owners): 7 pairs at the head and 7 at the base, the same
  pairs; 0 new.
- **Pre-ship:** each new module and `Extended`, `Simulation`, `Classes` and the facades
  elaborated on `oleans-cl161-cl160` before the PR was opened. No new name clashes with an
  existing declaration.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate162-ram-tier2-statements-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
