# RAM fill (Codex), tier 2 job D: the instruction phases (`Sim/Phases`, 2 admissions)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-phases`. **Base:** the commit given in the dispatch prompt, on
`complexity/ram-simulation`.

## What this is

`TCSlib/Complexity/RAMSimulation/Sim/Phases.lean` states one phase per instruction of the
extended word RAM (`WordRAM.XInstr`, `Programs/WordRAM/Extended`). A phase is a machine on the
eight tapes of `WordRAM.Sim.Encodes` (`Sim/Encoding`). From tapes encoding `c`, whose current
instruction is `ins`, it reaches tapes encoding the next configuration `xstep P x ρ c`, and
exits at `next` or `jump`. **This job proves the two statements:**
1. **`WordRAM.Sim.exists_phase`** (every non-verdict instruction): a nondeterministic machine
   whose two transitions differ only at a `coin` phase's entry, which is never re-entered. Its
   run is stated for each fixed choice `b` (`Turing.NDTM.fixChoice`), within
   `C·((|T| + 1)·(W + 1) + W² + |x| + 1)` steps and radius
   `C·((|T| + 1)·(W + 1) + log |x| + 1)`.
2. **`WordRAM.Sim.exists_verdictPhase`**: in verdict mode emit `v`, then halt.

Job E builds the phase host and the induction from these. Gate 162's auditor checked both
(G162-21, G162-22).

## Route

**Build each phase from the rows, by cases on `ins`.** Place five-tape rows on the eight tapes
with `Turing.Contract.embed` (`Build/Contract/Embed`) or `Turing.embedEmitTM`. Turn
`ReachesWithin` rows into contracts with `Turing.Contract.ofReaches`, and sequence them with
`Turing.Contract.seq` (`Build/Contract/Seam`).
- **Key of a written address `i`:** `Turing.exists_wordIntTM i a` into tape `1`.
- **Key of a computed address `[j]`:** look `j` up into a register, then
  `Turing.exists_wordSignExtendTM a` into tape `1`.
- **Operands** are looked up into registers `2` and `3` (`Turing.exists_keyLookupTM`). The result
  is computed into register `4` and stored back (`Turing.exists_keyAssignTM`).

| Instruction | Compute |
|---|---|
| `one i` | `exists_wordIntTM 1 0` |
| `add`, `sub`, `mul` | `exists_wordAddTM`, `exists_wordSubTM`, `exists_wordMulTM` |
| `load i j` | look up `[j]`, sign-extend it to a key, look that up |
| `store i j` | look up `[i]`, sign-extend it as the key, assign `[j]` |
| `half i j` | `exists_wordHalfTM` |
| `rdIn i j` | look up `[j]`, then `Turing.exists_inputBitTM` (with tape `5`) |
| `bltz i l` | look up `[i]`, `Turing.exists_wordSignTM`, exit at `jump` or `next` |
| `emit i` | look up `[i]`, `Turing.exists_wordNonzeroTM`; in function mode emit the bit in one step (in verdict mode, nothing) |
| `coin i` | one choice step at the entry: transition `b` remembers `b` in the state; then `exists_wordIntTM b 0` into register `4`, and assign |

The semantics come through `WordRAM.xstep_def`, `WordRAM.effect_def`, `WordRAM.inBitWord_def`,
`WordRAM.coinWord_def` and `WordRAM.XInstr.touches_def`, never by unfolding.

**The invariant.** `TableOf` is kept because:
- every key written is that of a cell of `T ∪ touches` in range: `ImmBound` for written
  addresses, and a word's signed value is in range (`WordRAM.toInt_wd` and the range lemmas of
  `Programs/WordRAM/Steps`);
- keys of distinct cells in range are distinct (`bvBits_injective`, and `BitVec.ofInt` injective
  on the range).

Lookups are correct for every read. Write these as lemmas once, about `TableOf`, `keyLookup` and
`keyAssign`, in a new file (below), and use them in every case.

**Nondeterminism.** Build each phase as a deterministic machine, made an `NDTM` by
`MultiTapeTM.toNDTM` (equal transitions). The coin phase is the exception: a fresh entry state
whose transitions under `false` and `true` go to two deterministic continuations. Its
`fixChoice b` is then the continuation for `b`, prefixed by one step. Make the entry a state that
no transition targets.

**Bounds.** The table has at most `|T|` entries of `O(W + a)` cells, so every lookup and
assignment costs `O((|T| + 1)·(W + 1))`. `mul` adds `O(W²)`; `rdIn` adds `O(W + |x|)` steps and
`O(W + log |x|)` radius. `C` depends on `a` and `ins`.

## Owned files

- `TCSlib/Complexity/RAMSimulation/Sim/Phases.lean`: the two statements, byte-identical.
- **New files** under `TCSlib/Complexity/RAMSimulation/Sim/`, named `Phase*.lean` (for example
  `PhaseTable.lean` for the `TableOf` lemmas and `PhaseRows.lean` for the placed rows). Their
  declarations are public in `WordRAM.Sim`, per the tier 2 addendum. `Phases.lean` imports them.
  Add each to the `RAMSimulation.lean` facade's imports and contents: you may edit the facade
  for that only.

## Admitted dependencies allowed

The statements of `Build/WordArith` (job A), `Build/KeyTable` (job B) and `Build/InputBit` (job C).
Nothing else.

## Downstream check

`RAMSimulation/Simulation`, `RAMSimulation/Classes` and the facades.
