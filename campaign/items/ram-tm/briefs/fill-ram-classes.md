# RAM fill (Codex): tier 3, the class corollaries (`RAMSimulation/Classes`, 9 admissions)

Read `COMMON.md` (bundled) first; its rules bind. **Fill name:** `fill-ram-classes`.
**Base:** the commit given in the dispatch prompt, on `complexity/ram-simulation`.

## What this is

`TCSlib/Complexity/RAMSimulation/Classes.lean` puts a language into a complexity class from a
word-RAM program that decides it. Its nine theorems are the corollaries of stage 2's simulation
theorems. Their statements were audited on 2026-10-14 and rechecked against the base on
2026-11-17; they are frozen. **This fill proves all nine.** It is bound arithmetic and
unfolding of class definitions through their published readers.

**Admitted dependencies** (corrected after gate 160, G160-01). The prescribed routes cite six
declarations that are, or were, admitted:

| Declaration | Home | Status |
|---|---|---|
| `WordRAM.exists_simulation`, `WordRAM.exists_ndSimulation` | `RAMSimulation/Simulation` | tier 2; **admitted** at your base |
| `WordRAM.wordSizeComputable_logSpace`, `wordSizeComputable_of_spaceConstructible` | `RAMSimulation/WordSize` | tier 1; admitted at your base unless the dispatch prompt says tier 1 has landed |
| `WordRAM.HaltsWithin.mono`, `WordRAM.HaltsWithin.touches_le` | `Programs/WordRAM/Extended` | tier 0; this fill is dispatched only after tier 0 has proved them, and the dispatch prompt names the base that includes them |

Use them as they are stated. Your proofs must contain no `sorry`. A `#print axioms` that shows
`sorryAx` cannot tell which admitted declaration was reached. So for each target, `REPORT.md`
lists the admitted declarations its proof reaches. Run a scratch dependency walk that collects
every constant reachable from the target whose value uses `sorryAx`. The chapters 3–4 probe
`CloseHeadlines` does exactly this; adapt it. The list must be a subset of the table above.

## Targets (in `WordRAM`, all in the owned file)

| Target | Uses |
|---|---|
| `mem_DTIME_of_decides` | `exists_simulation` (verdict mode, `fn := false`) |
| `mem_P_of_decides` | `mem_DTIME_of_decides`, `HaltsWithin.touches_le`, `HaltsWithin.mono` |
| `mem_P_of_decides_logWord` | `mem_P_of_decides`, `wordSizeComputable_logSpace` |
| `mem_SPACE_of_decides` | `exists_simulation` (verdict mode) |
| `mem_LOGSPACE_of_decides` | `mem_SPACE_of_decides`, `wordSizeComputable_logSpace` |
| `computesInSpace_of_computes` | `exists_simulation` (function mode, `fn := true`), `wordSizeComputable_logSpace` |
| `mem_SPACE_mul_of_decides` | `mem_SPACE_of_decides`, `wordSizeComputable_of_spaceConstructible` |
| `mem_NSPACE_of_accepts` | `exists_ndSimulation` |
| `mem_NL_of_accepts` | `mem_NSPACE_of_accepts`, `wordSizeComputable_logSpace` |

Each target's docstring has a proof sketch. The maintainer checked them against the definitions
at the base:

- **The classes** (rechecked at the base):
  - `Complexity.DTIME T = {L | ∃ c M, M.DecidesInTime L (c * T ·)}`, with
    `FinTM.DecidesInTime M L T = ∀ x, M.ComputesInTime x [indicator L x] (T |x|)`;
  - `Complexity.mem_P_iff : L ∈ P ↔ ∃ C d M, M.DecidesInTime L (C * (· + 1) ^ d)`;
  - `Complexity.SPACE s = {L | ∃ c M, M.DecidesInSpace L (c * s ·)}`, where
    `FinTM.DecidesInSpace` is `ComputesInSpace` of `x ↦ [indicator L x]`, and
    `ComputesInSpace M f s` is `∀ x, ∃ t, M.ComputesInTime x (f x) t ∧ spaceUsed (initCfg x) t ≤ s |x|`;
  - `LOGSPACE = SPACE logSpace`, `NL = NSPACE logSpace`;
  - `NSPACE s = {L | ∃ c N, N.DecidesInSpace L (c * s ·)}`, where `FinNDTM.DecidesInSpace N L s`
    is `∀ x, ∃ T, N.tm.HaltsWithin x T ∧ (∀ w, w.length = T → spaceUsedWith w (initCfg x) ≤ s |x|) ∧ (x ∈ L ↔ N.AcceptsWithin x T)`.

  **Read them only through these published readers** (the last four rows were added for this
  fill by PR #370, which your base includes):
  - `Complexity.mem_P_iff`, `Turing.FinTM.decidesInTime_iff`;
  - `Complexity.mem_SPACE_iff`, `Turing.FinTM.decidesInSpace_iff`,
    `Turing.FinTM.computesInSpace_iff`, `Complexity.LOGSPACE_eq`;
  - `Complexity.spaceConstructible_iff`, `Complexity.logSpace_eq`
    (`1 ≤ logSpace n` follows by `rw [logSpace_eq]; omega`);
  - **new:** `Complexity.mem_DTIME_iff`;
  - **new:** `Complexity.mem_NSPACE_iff`, `Turing.FinNDTM.decidesInSpace_iff`;
  - **new:** `Complexity.NL_eq`;
  - **new:** `WordRAM.outputOf_false`, `WordRAM.outputOf_true`, `WordRAM.simTime_eq`,
    `WordRAM.simSpace_eq`.

  Do not unfold the definitions themselves.
- **The simulation's output** `outputOf fn v o` is `[v]` in verdict mode (`outputOf_false`) and
  `o` in function mode (`outputOf_true`). `simTime` and `simSpace` are read through `simTime_eq`
  and `simSpace_eq`. All four are new readers in `Simulation.lean` (PR #370).
- **Monotonicity:** `Turing.FinTM.ComputesInTime.mono` moves a halting time up.
  `HaltsWithin.mono` and `HaltsWithin.touches_le` (`Programs/WordRAM/Extended`) give a run fixed
  bounds `T |x|` and `F |x|`.
- **`mem_P_of_decides`:** take `T n = C·(n + 1)^d` and `F n = 3·C·(n + 1)^d`. Then
  `TW n + (T n + 1)·(F n·(W n + 1) + W n² + n + 1)` is at most a constant times
  `(n + 1)^(3d + 1)`. Discharge it with `Nat.pow_le_pow_right` and `nlinarith`, or a short
  private polynomial lemma.
- **The space grades** use `logSpace n ≥ 1`, and `logSpace ≤ S` from `SpaceConstructible`
  (read through its published iff, not unfolded).
- **The constants:** `exists_simulation` gives `A`. Bound `simTime A …` by `(A + 1)·a·T' n` and
  `simSpace A …` by `(A + 1)·a·s n`, then use `(A + 1)·a` as the class constant.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/RAMSimulation/Classes.lean`. Do not change imports. Existing statements stay
byte-identical. You may change only the target bodies, their proof sketches, and the module
docstring's "proofs pending" note once all nine are proved.

## Downstream check

Classes is a leaf: nothing in `TCSlib/` imports it except the facade
`TCSlib/Complexity/RAMSimulation.lean`, if present. Elaborate that facade too.
