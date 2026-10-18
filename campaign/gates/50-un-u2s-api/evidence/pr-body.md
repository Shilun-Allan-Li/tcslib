## API for the C1-UN and U2-S continuations

These are two gaps that the reviews of the C1-UN and U2-S deliveries found (2026-10-17; the
reviews are `campaign/fills/c1/reviews/universal-1/REVIEW.md` and
`campaign/fills/u2s/reviews/startup-1/REVIEW.md`). The user ruled on 2026-10-18 that both are
published before either continuation issues.

| File | Additions |
|---|---|
| `TuringMachine/Build/Primitives` | `FinTM.pairExtractTM_fst_run`: on `pairEncode a b`, the extractor `pairExtractTM true false` first halts after exactly `4·|a| + 5` steps, in the whole configuration (output `a`, input head at `2·|a| + 3`, its work tape `bufferTape a` with the head one past). `FinTM.pairExtractTM_fst_run_budget` is the same at the published budget `5·(|z| + 1)`. Two private helpers. |
| `TuringMachine/Simulation` | `FinTM.bufferedSecondCfg_workTapes_cast` and `_workTapePos_cast` (`rfl`): the second phase's fields at the buffered composite's own tape-index type, through `Fin.cast (bufferedCompTM_k M₁ M₂)`. The published `simps` fields are stated at `Fin (M₁.k + (1 + M₂.k))`, which a consumer can reach there only by unfolding. |

### Checks (maintainer, against `oleans-lx2b`)

- **Elaboration:** both modules, 0 errors. No warning comes from the new lines; `Primitives`'
  existing linter notes are unchanged.
- **Axioms:** all four new names use `propext`, `Classical.choice` and `Quot.sound`.
- **Freeze:** `Primitives` 47 → 49 publics and 234 → 236 privates; `Simulation` 60 → 62 publics.
  Additions only.
- **Lint:** `TuringMachine/` 0 FAIL, 63 WARN.
- **The reviews' probes:** the extractor lemma resolves UN-1's setup step (the UN review's
  out/30–33). The cast pair rewrites under a seal of `bufferedCompTM` and its neighbours, where
  the published fields fail (the U2-S review's out/38–39).

### Replay (at the merged campaign state)

#129, #130 and #131 have merged. The campaign branch was merged into this one (`91154701`; its
Lean diff from the tip is exactly the two files above), and `replay-l132.sh` replayed
`Build/Primitives`' and `Simulation`'s downstream closure, 314 modules, which contains every module
#124 and #129–#131 changed, into a copy of #131's snapshot. **Passed (2026-10-18):** 314 of 314,
0 failed, static-equal (93).

### Gate

Gate 50 (`campaign/gates/50-un-u2s-api/`): pending.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

