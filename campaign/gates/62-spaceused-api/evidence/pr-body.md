**The space measure as a sum, and a head-radius space bound** (an API PR). Two public lemmas, no
existing declaration changed:

| File | Lemma |
|---|---|
| `TuringMachine/Deterministic` | **`Turing.MultiTapeTM.spaceUsed_eq_sum`**: `tm.spaceUsed cfg t = ∑ i, tm.spaceUsedByTape cfg t i`, by `rfl`, beside the definition (a specification-API equation; the vendored header's local-modifications list and the "Main definitions" section name it) |
| `TuringMachine/Finite` | **`Turing.MultiTapeTM.spaceUsed_le_of_abs_le`**: if every work head stays within `r` cells of its start up to time `t`, then `tm.spaceUsed d t ≤ k * (2 * r + 1)`. Beside `spaceUsedByTape_le_card_Icc`; proved from the equation and that per-tape bound only. The module's "Main results" list names it |

**Why.** F3 continuation 2's pre-ship (B6, the configuration-count runner
`Turing.exists_configWindowRunnerTM`) found no published route to the target's space clause
(`R.spaceUsed d t ≤ (K + 1) * (2 * C * (L + 1) + 1)`) under the no-unfolding rule. `spaceUsed` has
no equation as the sum of the per-tape counts, and the windowed runner's radius bound `wr_space`
is private (in `Build/WindowRun`) and reads the definition. A control in the pre-ship shows the
sum step closes with nothing sealed and fails with `spaceUsed` sealed. **The user ruled
(2026-10-22): an API PR first, with the equation and the radius lemma.** F3 continuation 2 cites the
radius lemma (its envelope clause is exactly the lemma's hypothesis at `r = C * (L + 1)`). Re-pointing
`wr_space` to it is a later dedup item.

**Commits:** `e172b914`, on the campaign branch at `0416ffea` (after #144); `097f3e04`, the
campaign branch merged in after #145, #146 and #148 (no conflict; the two files unchanged).

### Checks (maintainer, against `oleans-lsk2`, the tip's tree)

- **`Deterministic`** at the head, with `#print axioms` appended: 0 errors, 0 warnings;
  `spaceUsed_eq_sum` on `[propext, Classical.choice, Quot.sound]`.
- **The radius lemma** (the snapshot predates the equation, so `Finite` cannot be elaborated
  against it): its proof verbatim, citing a stand-in for the equation (same statement, by `rfl`,
  declared before the seal), with `MultiTapeTM.spaceUsed`, `spaceUsedByTape`, `visitedByTapeHead`
  and `runFrom` sealed: 0 errors, 0 warnings; `[propext, Classical.choice, Quot.sound]`. Its four
  `rfl` controls close unsealed and fail sealed. The replay elaborates the real `Finite`.
- **Freeze:** `Deterministic` 40 → 41 public, `Finite` 25 → 26 public; nothing removed or changed.
- **Lint:** `TuringMachine` 0 FAIL, 64 WARN over 82 files, at the base and at the head. No line over
  100 characters.

### Replay

`replay-lspapi.sh`, the merged tree `097f3e04`: the downstream closure of every file changed since
#144's merge (324 modules: `Deterministic`'s downstream, which contains the merged #145, #146 and
#148), chained from `oleans-lsk2`. **Pending.** #147 (U2-S) also overlaps this closure: merge this
PR first; #147 then re-replays its six modules.

### Gate

An API gate (gate 62). **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)


