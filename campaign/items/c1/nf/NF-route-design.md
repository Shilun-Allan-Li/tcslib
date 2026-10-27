# NF: the linear normal form's route, before its brief (design note, maintainer, 2026-10-27)

**What this is for.** NF is `Turing.FinNDTM.exists_codeNDTM_accepts_linear`
(`ClassNP/NDNormalForm.lean:78`), one of the two contracts `Complexity.ntime_hierarchy` rests on
since #172 (the other is E-D's `exists_diagonalizer`). It is in its own module, so its fill can run
beside E-Q's and E-D's. Megafill D's triage (T3) found it blocked on the controller-stopped
writer's contract (the user's ruling of 2026-10-17). That contract was drafted
(`campaign/items/c1/nf-writer/WriterControllerDraft.lean.txt`) and never landed. This note
re-checks the C1 design's route (`C1-design.md` §2.4, steps N1–N7) against the tree, and fixes
what lands before the brief. Its decisions are at the end. It starts from the docstring's sketch:
guess the display, then verify it in `k + 1` sweeps.

**The statement** (frozen). For every `N : FinNDTM Bool` there are `M : CodeNDTM` and `C` with:
- forward, `N.AcceptsWithin x t → M.toFinNDTM.AcceptsWithin x (C * (t + 1))`;
- backward, `M.toFinNDTM.AcceptsWithin x t → ∃ t', N.AcceptsWithin x t'`.

`CodeNDTM` fixes **two** binary work tapes and states `Fin (numStates + 1)` (`NDCodes.lean:99`).
`AcceptsWithin x t` is a choice word of length exactly `t` whose run halts with output `[true]`
(`ClassNP/NTIME.lean:96`). The backward direction is unbounded and claims no all-branch halting,
so runaway guesses may run forever.

## What is published (at the tip `43fe918f`, Lean `940671e0`)

- **The choice writer** `Turing.ndWriterTM k j q₀ δ stop bounded` (`Build/NDHost.lean:203`), the
  definition of both flavors. Only the bounded flavor has a contract:
  `ndWriterTM_run_block` (`:351`), with the trivial controller over a nonblank block of `m` cells,
  every word of length `m + 1` reaching `done` at the same time. The controller-stopped flavor
  (`bounded := false`, a real `stop`) has **no contract**. The draft's statement is
  `ndWriterTM_run_controller`: if the controller first stops after `m` written bits, the prefix
  `w.take (m + 1)` writes `w.take m` from the head and reaches `done`, and no prefix of length at
  most `m` does. Its proof generalizes the bounded proof's private helpers (`wr_cfg` from `Unit`
  to any `Q`, with state `run ((w.take i).foldl δ q)`; `wr_tape_append` is `Q`-independent).
- **The guess-then-run host** `Turing.guessRunTM` (`:538`), with `guessRunTM_runWith`,
  `_haltsWithin` and `_accepts_iff` (`:1013`). **It composes only the bounded writer**, whose block
  length `m` the deterministic setup fixes before the guess. NF's display has length `W · t` for an
  unknown `t`, so `guessRunTM` cannot carry it. Its lemmas assume the bounded writer's synchronized
  timing (every branch guesses for exactly `m + 1` steps), so a controller-stopped variant needs
  its own run and acceptance lemmas. E-D's route cites `guessRunTM` as it is, so the variant is
  added beside it, not by changing it.
- **The phase hosts**: `Turing.NDTM.phaseHostND` with `phaseHostND_run` (`:93`, `:143`) for the
  nondeterministic composition, and `Turing.phaseHostTM` (`Build/Seam`) for the deterministic
  verifier's phases.
- **Rewinds and steps**: `skipTM`, `skipBackTM` (`Build/Catalog`), as `toNDTM` in the host.
- **The output summary**: `outputSummary`, `summaryEmit` and their laws (`Build/StepBlock.lean:142–198`),
  public, for sweep 0's check that the output is exactly `[true]`.
- **The packaging**: `Turing.NDTM.relabelState` with `relabelState_runWith`
  (`TuringMachine/Nondeterministic.lean:474, 488`), for the `Fin (numStates + 1)` states.
- **The run algebra**: `NDTM.runWith_nil`, `_cons`, `_append`, `runWith_of_halt`,
  `AcceptsWithin.mono`, `acceptsWithin_iff`, `MultiTapeTM.toNDTM`'s run equations, and the
  deterministic `step_of_some` and `Action.apply_*` field equations for own leaves.
- **Not usable here, but models:** StepBlock's public fixed-field reader `recordTM` and its
  `recordTM_effect` (the universal machine's H2 record, on `k + 2` tapes: a record tape, a summary
  cell and a mirrored bank). NF has two tapes in all, so its sweeps are new leaves.

## The shape (recommended)

`M` is the controller-stopped guess-then-run variant on tape A (tape 0). It guesses, rewinds A
and runs a deterministic two-tape verifier `V`, followed by the verdict bit. All of it is
relabeled into `Fin`.

**The display.** One record per step of `N`, of fixed width `W = 2k + 4`:
- the choice bit `bᵣ`;
- the `k + 1` claimed reads `σᵣ` (the input's and each work tape's), each `Option Bool` in a
  2-bit block;
- the end flag `endᵣ`.

**The guess** (N1). The controller is `Q := Fin W × Bool` (the position in the record, and
whether the last completed record carried the end flag). It stops at a record boundary after an
end-flagged record. A branch that never sets the flag never stops, which the statement allows.

**The verifier `V`** (deterministic, tapes A and B, the native input head). It runs these phases
under `phaseHostTM`, each followed by a rewind of A by `skipBackTM`:
1. **Sweep 0** (N2), a finite-state scan of A. It tracks `N`'s state from `q₀` and recomputes
   `aᵣ := N.tm.tr bᵣ qᵣ σᵣ` (the per-step actions are recomputed, never guessed). It checks that
   `endᵣ` is set exactly when `aᵣ` halts. It tracks the output summary through `summaryEmit`, and
   rejects unless the summary at the end is `[true]`'s.
2. **Sweep 1** (N3): the input claims. Each record's recomputed action moves the native input
   head; the claimed input read must equal the cell under it. Then the input head returns to its
   start, by a fixed seek (`exists_inputSeekTM`) or by reversing the recorded moves.
3. **Sweeps 2 … k + 1** (N4), one per work tape `j`. Tape `j` is replayed on B as 2-bit blocks
   `(visited, symbol)`, so that the visited region is contiguous and nonblank. B's head follows
   tape `j`'s claimed head (a move of `d` cells is `2d` cells on B). Each claimed read is checked
   against B's block, and the recomputed write is applied. Then B is cleared over the visited
   region and its head returned.
4. **The verdict**: accept iff every sweep passed.

Each sweep is one own-file finite-state leaf. It is a single machine reading A one cell per step,
with its run lemma by induction over records through `step_of_some`, not a private loop driver.

**The ledger.** The guess takes `W · t` steps for `t` records. Each sweep and rewind takes
`O(W · t)`, B's replay `O(W · t)` and its clear `O(W · t)`. In all `M` runs within
`C_N · (t + 1)`, with `C_N = O(k · W)`; the `+ 1` covers `k = 0` and `t = 0`.

**The transfers** (N6), each by induction on records:
- **Forward:** an accepting run of length `t₀ ≤ t` gives its display, `t₀` records with the flag on
  the last. The word that guesses it passes every sweep within `C_N (t₀ + 1)`; pad it to exactly
  `C · (t + 1)` (`runWith_of_halt`).
- **Backward:** a passing display is a genuine run. If the claimed reads up to `r − 1` are
  genuine, so are the recomputed actions, so each replayed tape at `r` is genuine, so sweeps 1 to
  `k + 1` make `σᵣ` genuine. The run halts at the flagged record with output `[true]`, so
  `N.AcceptsWithin x t'` holds with `t'` the record count.

**The packaging** (N5): the host's state type is finite, since every phase's is. Relabel it by
`Fintype.equivFin` into `Fin (card − 1 + 1)`, through `relabelState` and `relabelState_runWith`.

## What lands before the brief

**A maintainer API PR in `Build/NDHost`**, additive (no existing statement changes):
1. `ndWriterTM_run_controller`, the drafted contract, proved by generalizing the bounded proof's
   helpers (the B5a and H precedent of a maintainer landing in place of a fill).
2. **The controller-stopped guess-then-run host**, beside `guessRunTM`. It has the same phases,
   with the controller writer on a blank tape and no setup block. It needs a handoff lemma at the
   word-dependent guess time and an acceptance lemma: some word of length exactly `B` accepts iff
   some stopped stream makes `V`'s first verdict `acc` with an empty output, at every `B` beyond
   the run's time. There is no all-branch halting lemma; NF claims none.

It needs its gate, and a replay of `NDHost`'s downstream closure.

**Then NF's brief** owns `ClassNP/NDNormalForm.lean`: the record layout, the verifier's leaves,
the transfers and the packaging. It can run beside E-Q cont1 and E-D (different files). Its first
edit is the imports the API PR's rows need.

## Leaves and sizes (ESTIMATE)

| Piece | Where | Lines |
|---|---|---|
| The controller contract | the API PR (`NDHost`) | 100–200 |
| The controller guess-run host and its lemmas | the API PR (`NDHost`) | 400–700 |
| The record layout and its encoders and decoders | NF | 150–300 |
| Sweep 0, sweep 1, the tape sweep (parameterized by `j`), B's clear | NF | 1,200–2,500 |
| The verifier's phase composition | NF | 200–400 |
| The transfers, forward and backward | NF | 500–1,000 |
| The packaging and the ledger | NF | 150–300 |

The API PR is **0.5–0.9k**, and NF **2.2–4.5k** (the C1 plan's 2.5–5k for both).

## Copy hazards the brief names

- `ClassNP/ExhaustiveReplay` (`xr_` privates: replays of a fixed NDTM on a choice word), and
  `Nondeterminism`'s private `choiceCore` replay: run decompositions to cite or to avoid copying.
- `Build/StepBlock`'s `recordTM` and B5a's private `h1*` record family (`CodeSimulator`): models
  for a fixed-width reader, not citable on two tapes.
- `Build/NDHost`'s private `wr_*` helpers: the API PR generalizes them in place, so the fill
  never needs them.
- TR-1's truncation copies (`campaign/duplication-ledger.md`), if the transfer truncates an
  acceptance.

## Decisions

1. **The controller contract** (the 2026-10-17 ruling was a statement PR, then a W continuation
   to fill it).
   - (A) **Land it proved, by the maintainer API PR above. Recommended:** it is a small induction
     on the bounded proof's own helpers, in their own file, and saves a fill round.
   - (B) Keep the ruling: a statement PR, its gate, then a fill.
2. **Where the controller guess-run host lives.**
   - (A) **`Build/NDHost`, in the same API PR, beside `guessRunTM`. Recommended:** it is a host,
     like `guessRunTM`, and NF's file would otherwise re-derive host-level reasoning.
   - (B) Composed privately in `NDNormalForm` over `phaseHostND`.
3. **The display's end.**
   - (A) **A guessed end flag per record, checked in sweep 0. Recommended:** the C1 design's
     choice; the controller stays a counter and every check is deterministic.
   - (B) A controller that simulates `N`'s control and stops when the recomputed action halts:
     no flag, but a controller over `N`'s states and a partial record.
4. **The queue.** NF's brief issues after the API PR lands, and can run beside E-Q cont1 and E-D
   (different files). The agent is a separate question.
