# PR #124's body, as retrieved 2026-10-17 (head `0355da56`)

## The step block's seam layout from a captured serialization (a statement PR)

**The gap (G2).** C1-R's partial delivery was reviewed on 2026-10-17
(`audits/evidence/c1/fills/core-1/REVIEW.md`, gap G2). The review found that the step block's
represented start (`StepBlock.Rep`) needs two exact auxiliary tapes:
- the bare table `tableBitsK tr` on the table tape;
- the unary initial state from cell `2` on the summary tape.

Every startup instead captures the whole serialization,
`serializeK M = pairEncode n.bits (unaryFin M.q₀ ++ tableBitsK M.tr)`. No public machine
redistributes it. U2-S (in flight) plans that split privately, and H1's sketch and R's route
need it too.

**The ruling (user, 2026-10-17):** one public contract, stated now in its own statement PR with
its gate.
- R and UN cite it.
- U2-S's private leaf is promoted to prove it when U2-S delivers.

**Stacked on #123** (C1-W's landing, itself on #122): the replay closures overlap through the
`TuringMachine` facade. Merge #121, #122 and #123 first.

### What

| File | Change |
|---|---|
| `TuringMachine/Build/SeamLayout` (new) | `Turing.exists_seamLayoutTM`, sorried: for distinct tapes `src`, `tbl`, `sm`, one machine takes `src` holding `pairEncode a ((List.replicate q true ++ [false]) ++ v)` (head anywhere in the word, or just past it) to `tbl` holding `v` and `sm` holding the unary word from cell `2`, with `src` cleared, the three heads at `0`, everything else unchanged, no emission, within `C·(|s| + 1)` steps and not before |
| `TuringMachine` (facade) | imports and lists the module |

At `a = n.bits`, `q = M.q₀` and `v = tableBitsK M.tr`, the start word is `serializeK M`, and the
end gives `Rep`'s table and summary fields for an empty output. The consumer probe
(`audits/evidence/c1/seam-layout/`) derives both through published equations, using #122's
`FinTM.bufferTape_of_neg`.

### Checks (maintainer, against `oleans-lndnf`)

- **Elaboration:** 0 errors; 1 warning, the contract's `sorry`.
- **Consumer probe:** 0 errors; only the contract's `sorry`.
- **Lint:** `TuringMachine/` 0 FAIL, 63 WARN, unchanged (the new module adds an INFO row only).
- **Replay:** `replay-lseam.sh`, the module and the facade (2 modules), chained from `oleans-lc1w`
  (#123's replay).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

