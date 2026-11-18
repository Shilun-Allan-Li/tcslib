# Tier 2 design note: the word RAM on Turing machines (`exists_simulation`, `exists_ndSimulation`)

2026-11-18 (maintainer, at Seyoon's request). Base: `complexity/ram-simulation` after #371
(`adb694d2`; snapshot `oleans-cl161-cl160`). **Seyoon ruled on D1–D5 the same day** (§6). The jobs
are §5's regrouped table.

## 1. What is left, and what the statements ask

After #371 the RAM work has 11 admissions: `Simulation` 2 (this tier) and `Classes` 9 (tier 3,
dispatched). The two targets were gated on 2026-10-14 and are frozen. The re-read of
2026-11-18 found them sound. It checked word size `W = 0`, the immediate addresses, the range
of `rdIn`, `HaltsWithin`'s `n < t` and the matching of choice words to coin streams both ways.

The proof builds one machine, `M : FinTM Bool`, depending on `P` and `fn` only. Per input
`x`, with `n = |x|` and `W = W n`:

- **Time:** `TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)`. `ComputesInTime` means halted by then,
  with exactly `outputOf fn v o` on the output.
- **Space:** `SW n + A·(f·(W + 1) + W + logSpace n + 1)` work cells. The input and output tapes
  do not count, so the input must be read in place.
- **Nondeterministic form:** the same machine, with each `coin` a choice step. Bounds are
  uniform over branches. A branch is accepting when its output is `[true]`
  (`FinNDTM.AcceptsWithin`).

## 2. What the library already gives (surveys of 2026-11-18)

All of these are public and proved unless marked otherwise.

| Need | Exists | Gap |
|---|---|---|
| Composition | `Turing.Contract` (exact time, endpoint, no earlier exit, head envelopes), `trans`, `seq` (seams), `inPhase` (phase host), `branch`, `embed`, `mapState`, counter-loop rounds | `inPhase` cannot redirect a phase to itself and cannot end in a halt (see §4) |
| Dispatch on the program counter | `phaseHostTM` (`Build/Seam.lean:886`) with its run lemmas | no space lemmas; space comes from contract envelopes |
| Nondeterministic dispatch | `NDTM.phaseHostND` and `phaseHostND_fixChoice` (`Build/NDHost.lean`): the host of fixed-choice phases *is* `phaseHostTM` | none |
| Choice slices | `runWith_eq_fixChoice_runFrom`, `spaceUsedWith_eq_fixChoice_spaceUsed`, `runWith_mapState_of_agreeOn(_det)`; the NARM compiler's `ndtm_runWith_eq_runFrom` (PATH ∈ NL): choice at `choose` states only, deterministic elsewhere | none; the NARM proof is the template for the coin phase |
| Word size start-up | `embedSilentTM` (output captured on a work tape), `expandTM` (binary `W` to a unary ruler of `W` cells), `exists_inputLengthTM` (`Nat.bits n` in `O(n)`) | the start-up composite |
| Input | `exists_inputSeekTM` (seek position `p ≤ n + 1` in `C·(|w| + pos + p + 1)`, scratch tape blank, restores the work tapes) | the range test `p < n` before it; contract wrappers (the row states `∃ t ≤ …`, contracts need an exact time) |
| Word rows | `copyTM`, `compareTM` (equality), `clearTM`, increment and decrement, `scanTM` (one-tape finite-state transducer: sign, shift, negation as instances), `writeConstTM`, the seek, skip and walk family | **no two-tape row with a carry** (add, subtract, less-than); **no multiplication** |
| The memory table | `RecordTable`'s layout (`tableFields`, `TableAt`, `TableWF`) and `exists_fieldsCopyTM` | **no keyed find** (the key on another tape), **no in-place overwrite**. `exists_tableFindTM` (finite-state predicate, not keyed) and `exists_tableAppendTM` are **admitted** on `main`, and tier 2 must not cite them |
| Output | any action may emit one bit | a one-step `emit` phase and the final "write `[v]`, halt" phase (trivial) |

## 3. The construction

**Tapes** (a fixed number, independent of `W`):
- the word-size machine's tapes, frozen after start-up (`SW n`);
- the ruler, `W` cells;
- the length tape, `Nat.bits n`;
- the table;
- three word registers: two operands and the result;
- a multiplication accumulator;
- the seek scratch tape, kept blank;
- the output, used only in function mode.

**Encoding:**
- *Words* are `W`-bit little-endian two's complement, measured against the ruler. A
  ruler-bounded lockstep scan handles `W = 0` (zero cells), where blank-delimited fields would
  not.
- *Keys* are addresses sign-extended to width `W + a`, where `a` covers `P`'s immediate
  addresses. So an immediate address and an equal computed address get the same key.
- *An entry* is the key, then the value, each with a leading marker bit, so that no field is
  empty and the table's end is a blank.
- *The invariant:* the tapes encode `XCfg` `c` when the phase is `c.pc` and the table lists
  exactly the cells written so far, plus `-1`, with their values. Every other cell reads 0.
  `HaltsWithin`'s footprint `K` then bounds the table by `|K| + 1 ≤ f + 1` entries.

**Start-up:**
1. Run the word-size machine silently. Its run lemma starts at the initial configuration.
2. Expand `Nat.bits W` into the ruler.
3. Rewind the input and count `n` onto the length tape.
4. Write the entry `-1 ↦ n mod 2^W`, truncating or padding `Nat.bits n` against the ruler.

Cost: `TW n + O(n + W²)` time and `SW n + O(W + logSpace n)` space. This fits the bound because
`t ≥ 1`.

**One phase per instruction position, in a phase host.** Each instruction is a short sequence of
rows:
- *find:* find the operand keys and copy the values into the registers;
- *compute:* apply the instruction to the registers;
- *write back:* overwrite the entry in place, or append it if absent;
- then dispatch to `pc + 1` or to `l`.

| Instruction | Compute |
|---|---|
| `one` | write the word `1` against the ruler |
| `add`, `sub` | two-tape scan with a carry |
| `mul` | shift-and-add, `W` rounds, `O(W²)` |
| `load`, `store` | sign-extend the address register into a key, then find |
| `bltz` | sign test (the top bit) |
| `half` | arithmetic shift |
| `rdIn` | range test `0 ≤ p < n` against the length tape, then seek and read |
| `emit` | zero test, then emit one bit (function mode only) |
| `coin` | write `0` (deterministic) or the choice bit (nondeterministic) |
| `accept`, `reject` | write `[v]` in verdict mode, then halt |

Every step costs at most `A·(f·(W + 1) + W² + n + 1)`:
- a table scan over at most `f + 1` entries of `W + O(1)` cells;
- `W` rounds of an `O(W)` scan for multiplication;
- `O(W + n)` for the seek.

**One induction, for both forms.** Build the host as an `NDTM` with `phaseHostND`. The coin phase
is the only state whose two transitions differ.
- *The master lemma:* by induction on the `XStepsIn` run, the branch with choice word `w`
  simulates `P` with the coin stream read off `w` at the coin steps. Between coin steps, it
  applies the deterministic contracts slice by slice (`phaseHostND_fixChoice`,
  `runWith_eq_fixChoice_runFrom`).
- *Deterministic form:* take `M = N.fixChoice false` and the all-`false` word. Its stream reads
  like `ρ = []`, so the deterministic form is a corollary.
- *Nondeterministic form:*
  - every branch is the run of some stream, so the uniform bounds bound every branch;
  - an accepting stream gives a branch that places its bits at the coin steps;
  - an accepting branch gives a stream whose run accepts, by `HaltsWithin.unique` (tier 0).

## 4. Hazards found in the survey

1. **`Contract.inPhase` forbids redirecting into the same phase** (`q.1 ≠ p`), but `bltz i l`
   with `l = pc` is a legal self-loop. Fix: index phases by (position, parity) and flip the
   parity at every dispatch. It costs nothing.
2. **`inPhase` cannot end in a halt** (`none ∉ X`). The verdict phase uses
   `phaseHostTM_run_le` instead, which is built for the last phase.
3. **The admitted table rows.** `exists_tableFindTM` and `exists_tableAppendTM` are `sorry` on
   `main`. A tier 2 route through them would leave `exists_simulation` resting on admissions. The
   keyed rows must be proved, and must not cite them.
4. **`W = 0`** gives empty words, so the layout must not rely on blank-delimited fields (§3).
5. **Existential rows.** `exists_inputSeekTM` and `exists_inputLengthTM` give `∃ t ≤ …`. A
   contract needs an exact time, chosen with `Classical.choose`, through a small adapter per row.
6. **The seek's scratch tape** must be blank everywhere (`∀ q, … = none`), so it is a dedicated
   tape that no other row writes.
7. **Private declarations do not cross files.** The simulation is 3,000–5,000 lines, and the
   policy's file size of at most about 1,000 lines forces several files. Their shared lemmas
   must then be public, in an internal namespace (decision D1).
8. **Stale line references** in `Simulation.lean`'s docstrings: `phaseHostTM` is at
   `Seam.lean:886`, not 813; `exists_inputSeekTM` is at `InputCall.lean:291`, not 294;
   `embedSilentTM` is at `Embed.lean:253`, not 241. These are repaired with the fill that
   rewrites the sketches.

## 5. The pieces, PRs and fills

The policy's **Hosts come first** rule decides the order. The keyed table is a dispatcher over a
data structure, so it is a host. Its public contract is stated and gated before any fill uses
it. The arithmetic rows are leaf rows, but `scanTM` almost covers them, so the general
two-tape form goes into the shared layer rather than into a private copy.

| # | Piece | Home (proposed) | Public? | Estimate (lines) |
|---|---|---|---|---|
| L1 | Lockstep transducer row: `r` source tapes and one destination, finite-state carry, bounded by a ruler tape. Instances: add, subtract, less-than, sign-extend, sign, zero test, arithmetic shift, copy | `Build/Lockstep.lean` (new) | yes: row plus instance lemmas | 800–1,500 |
| L2 | Multiplication mod `2^W`: a phase loop over the multiplier's bits, built from L1 | `Build/WordMul.lean` (new) | yes | 500–900 |
| L3 | Keyed table host: layout, find by a key on another tape, read value, overwrite value, append, rewind, with time and envelope clauses | `Build/KeyTable.lean` (new), reusing `RecordTable`'s layout | yes, statement-gated first | 1,500–2,500 |
| L4 | Contract adapters for the seek and length rows; the range test | `Build/InputContract.lean` (new) | yes | 300–600 |
| S1 | Start-up | `RAMSimulation/Sim/Startup.lean` | internal (D1) | 500–900 |
| S2 | The encoding invariant; the instruction phases and their contracts; the parity phase host | `RAMSimulation/Sim/Phases*.lean` | internal | 1,500–2,500 |
| S3 | The master induction; the bounds; the deterministic corollary | `RAMSimulation/Sim/Run.lean`, then `Simulation.lean` | internal; targets public (frozen) | 600–1,200 |
| S4 | The nondeterministic form: coin phase, slices, matching choice words to coin streams | `RAMSimulation/Sim/ND.lean`, then `Simulation.lean` | internal | 500–1,000 |

**Total: about 6,200–11,100 lines.** This agrees with the itemized 6,100–10,500 of 2026-10-12.

**The jobs** (Seyoon, D4: Codex in the local checkout, larger jobs than tiers 0–1, run in
parallel):

| Job | Pieces | Estimate (lines) | Can start |
|---|---|---|---|
| A | L1 and L2: the lockstep row with its instances, and multiplication | 1,300–2,400 | after the statement gate |
| B | L3: the keyed table host | 1,500–2,500 | after the statement gate |
| C | L4 and S1: the input contracts, the range test and the start-up | 800–1,500 | after the statement gate |
| D | S2: the encoding invariant, the instruction phases and the parity phase host | 1,500–2,500 | after the statement gate, against A–C's gated statements |
| E | S3 and S4: the master induction, the bounds, both targets | 1,100–2,200 | after the statement gate, against D's gated statements |

All five can run at once. Each cites the others' gated statements under the proved-modulo
rule, and lands once what it cites is proved.

**Sequence:**
1. **Statements PR** (maintainer):
   - sorried public statements of L1–L4;
   - S1–S3's internal interfaces, especially the encoding invariant, which every phase shares;
   - a statement gate (Codex audit).
2. **Jobs A–E in parallel** (table above), each against the gated statements.
4. **Landing:** each delivery through the gate kit, as with #371. `Simulation.lean` drops its last
   two admissions only when every piece below it is proved.

## 6. Decisions (Seyoon, 2026-11-18)

- **D1. New public homes. Approved as proposed.** The four new `Build/` modules L1–L4 with public contracts, and the
  simulation split over `RAMSimulation/Sim/*.lean` with public lemmas in an internal namespace
  (`WordRAM.Sim`), so that they can cross files. *Recommended:* yes. The alternative, one
  `Simulation.lean` of 3,000–5,000 private lines, breaks the file-size policy, and hosts-first
  forbids a private table.
- **D2. The table layout. Reuse `RecordTable`'s layout.** Reuse `RecordTable`'s `TableAt` layout with new keyed rows in
  `Build/KeyTable.lean` (*recommended*: one table layout in the library), or a separate layout
  tuned to the RAM.
- **D3. One master induction. Approved.** on the nondeterministic host, with the deterministic form as its
  `fixChoice false` corollary (*recommended*: one induction instead of two), or two separate
  machines.
- **D4. Fill routing.** Proposed: Codex fills, one piece per fill. **Ruled:** "codex in local
  checkout, but 600-1200 lines per job is too little. we can bite off more than that per job (in
  addition to running the jobs in parallel)". So the work goes as five larger jobs, A–E (§5), in
  parallel, through the exchange (Seyoon, 2026-11-17).
- **D5. The statement gate. A Codex statement audit.** for step 1: a Codex audit, as for the 2026-10-14 statement gate
  (*recommended*: these are new public APIs).
