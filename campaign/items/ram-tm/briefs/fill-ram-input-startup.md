# RAM fill (Codex), tier 2 job C: the input bit and the start-up (2 admissions, 2 files)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-input-startup`. **Base:** the commit given in the dispatch prompt, on
`complexity/ram-simulation`.

## What this is

Two statements of tier 2, in two owned files:
1. **`Turing.exists_inputBitTM`** (`Build/InputBit.lean`): with a signed word `u` on tape `0` and
   `Nat.bits |x|` on tape `1`, write on tape `2` the word `1` if `0 ≤ u.toInt` and the input bit
   at `u.toInt` is `true`, and `0` otherwise. It reads the input in place: `O(W + |x|)` steps,
   work radius `O(W + log |x|)`. Job D cites it for `rdIn`.
2. **`WordRAM.Sim.exists_startup`** (`RAMSimulation/Sim/Startup.lean`): for any word-size
   witness `Mw`, a machine with the eight tapes of `WordRAM.Sim.Encodes` first, and `k'` more,
   that reaches a configuration encoding `XCfg.init W |x|` over the cells `{-1}`. It does so
   within `tw + C·(|x| + W² + 1)` steps and `sw + C·(W + log |x| + 1)` visited cells, where `Mw`
   writes `Nat.bits W` within `tw` steps and `sw` cells. Job E cites it.

Each has a proof sketch. Gate 162's auditor found both achievable (G162-19, G162-20).

## Route: the input bit

1. **The sign test** (`Turing.exists_wordSignTM`, job A): a negative position writes `0`.
2. **The range test `u.toInt < |x|`.** Compare the little-endian value of `u`'s bits with
   `Nat.bits |x|`. The words have different lengths: the longer one's excess bits decide when they
   are nonzero. Write this private comparator once.
3. **Otherwise seek.**
   - Copy `u` to a scratch tape and increment it once. The input head's position `p + 1` holds bit
     `p` (`Turing.Cfg`'s input positions are shifted by one). No overflow is possible: the sign
     bit is clear and `u.toInt < |x|`.
   - Seek with `Turing.exists_inputSeekTM` (`Build/InputCall`): position word on its tape `0`, a
     blank scratch tape as its tape `1`. Place its two tapes with `Turing.embedEmitTM` or
     `Contract.embed`. It gives `p ≤ |x| + 1`, time `C·(|w| + pos + p + 1)`, work envelope
     `C·(|w| + 1)`, and its work tapes restored.
4. **Write the word.** Read the bit under the input head, write `1` or `0` over the register
   (`Turing.exists_wordIntTM`, job A), clear the scratch tapes, and return the heads. The input
   head ends where the seek left it, the `∃ ip` of the statement.

At `W = 0` the register is the empty word, whatever the bit.

## Route: the start-up

The statement's sketch has the steps:
1. Run `Mw` silently, its output captured on a work tape (`Turing.embedSilentTM`,
   `Build/Embed`). Its run lemmas give the time `tw` and its tapes' visited cells.
2. Make the registers. Expand `Nat.bits W` into `W` zeros (`Turing.expandTM`, `Build/CounterLoop`,
   with the pattern `[false]`), copy them to tapes `2` to `4`, and extend tape `1` to `W + a`
   cells.
3. Rewind the input (`Turing.inputRewindTM`) and count `|x|` onto tape `5`
   (`Turing.exists_inputLengthTM`).
4. Install the table `[(keyBits a W (-1), bvBits (wd W |x|))]`:
   - the key, by `Turing.exists_wordIntTM` with `c = -1`;
   - the value, as the low `W` bits of `Nat.bits |x|` padded with zeros, which is `wd W |x|`
     read modulo `2^W`;
   - then `Turing.exists_keyAssignTM` (job B) into the empty table, or a direct layout write.
5. Return every head to its origin, and exit. The origins `o` are the statement's existential.

`TableOf` holds: `-1` is in range because `1 ≤ a`, and `initMem` is `0` elsewhere
(`WordRAM.initMem_def`).

**Space:** `Mw`'s tapes and the capture tape, whose `|Nat.bits W| + 1 ≤ W + 1` cells are visited,
plus `O(W + log |x|)` on the eight. Use `MultiTapeTM.spaceUsed` through
`Turing.seamCompTM_spaceUsed_le_add_ofCfg` and the embedding's visited-set lemmas.

## Owned files

- `TCSlib/Complexity/TuringMachine/Build/InputBit.lean`
- `TCSlib/Complexity/RAMSimulation/Sim/Startup.lean`

Statements byte-identical. Private helpers in each file. Both files may add imports of existing
`Build/*` modules; `Startup.lean` may also import `RAMSimulation/WordSize` if needed. List each
import with its reason.

## Admitted dependencies allowed

The statements of `Build/WordArith` (job A) and `Build/KeyTable` (job B). Nothing else.

## Downstream check

`RAMSimulation/Sim/Phases`, `RAMSimulation/Simulation`, `RAMSimulation/Classes` and the
facades.
