## The step block's seam layout from a captured serialization (a statement PR)

**The gap (G2).** C1-R's partial delivery was reviewed on 2026-10-17
(`campaign/fills/c1/reviews/core-1/REVIEW.md`, gap G2). The review found that the step block's
represented start (`StepBlock.Rep`) needs two exact auxiliary tapes:
- the bare table `tableBitsK tr` on the table tape;
- the unary initial state from cell `2` on the summary tape.

Every startup instead captures the whole serialization,
`serializeK M = pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)`. No public machine
redistributes it. U2-S, H1's sketch and R's route all need that split.

**The rulings.**
- **User, 2026-10-17:** one public contract, stated now in its own statement PR with its gate. R
  and UN cite it.
- **User, 2026-10-18 (supersedes the 2026-10-17 plan that U2-S's private leaf would be promoted to
  prove it):** a standalone fill proves the contract after its statement gate. U2-S's continuation
  may import it.

**Base: the campaign branch.** #122, #123, #125 and #126 are in (#128 landed the last three), so
this PR's diff is its own two files.

### What

| File | Change |
|---|---|
| `TuringMachine/Build/SeamLayout` (new) | `Turing.exists_seamLayoutTM`, sorried: for distinct tapes `src`, `tbl`, `sm`, one machine takes `src` holding `pairEncode a ((List.replicate q true ++ [false]) ++ v)` (head anywhere in the word, or just past it) to `tbl` holding `v` and `sm` holding the unary word from cell `2`, with `src` cleared, the three heads at `0`, everything else unchanged, no emission, at one time `T ≤ C·(|s| + 1)`, depending on the word and the head's start only, and not before |
| `TuringMachine` (facade) | imports and lists the module |

At `a = n.bits`, `q = M.q₀` and `v = tableBitsK M.tr`, the start word is `serializeK M`, and the
end gives `Rep`'s table and summary fields for an empty output.

**Round 2 (gate 43's round 2, gate folder 46).**
- **The time:** `T` is chosen before the configuration, as the universal startup's suffix-uniform
  first exit needs (round-1 finding 2).
- **The sketch** (round-1 finding 1): eight phases joined by `phaseHostTM`. Six invoke catalog rows
  through their exact `_run_ofCfg` contracts: skip, skip back, a walk on `sm`, transfer, skip back
  and clear. The other two are the named leaves `pairSkip` and `unarySplit`. The exact time is
  `T = 2n − r + 4h + 5q + 2|v| + 23 ≤ 18(n + 1)`.
- **The probe** (round-1 finding 3): the round-1 probe only proved the two identities, with a
  local stand-in for `bufferTape_of_neg`. The round-2 probe
  (`campaign/items/c1/seam-layout/r2/`) applies the contract. It recovers the round-1 form and the
  universal startup's code-uniform exit with its tapes `k` and `k + 1`. From R1′'s capture
  endpoint it also derives `Rep`'s table and summary fields for the initial configuration, through
  #122's `FinTM.bufferTape_of_neg`, assembled by `Rep_iff`.
- **The docstrings** are worded in public-facing terms (`45b79f5f`).

### Checks (round 2, head `45b79f5f`)

- **Elaboration** (maintainer, against `oleans-lc1w`): 0 errors; 1 warning, the contract's `sorry`.
- **Consumer probe:** 0 errors; only the inline contract's `sorry`.
- **Lint:** `TuringMachine/` 0 FAIL, 63 WARN, unchanged (the new module adds an INFO row only).
- **Replay:** `replay-lseam2.sh`, the module and the facade (2 modules), chained from
  `oleans-lx2b`. **Passed (user, 2026-10-18):** 2 of 2, 0 failed, static-equal (1).
- **Gate:** round 2 returned **PASS 0/0/1/11**
  (`campaign/gates/43-seam-layout-statements/findings-r2.md`). Its one minor was this description,
  which still carried round 1's plan and identifiers; this text corrects it.

**Superseded (round 1, kept for the record):** round 1's checks ran against `oleans-lndnf`, and
its replay, `replay-lseam.sh`, was chained from `oleans-lc1w`. Round 1's gate returned
FAIL 0/2/1/7 (`campaign/gates/43-seam-layout-statements/findings.md`); round 2 replaces those
checks.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

