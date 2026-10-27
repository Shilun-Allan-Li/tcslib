# B6's H: the space hierarchy's route, before its brief (design note, maintainer, 2026-10-27)

**What this is for.** H is `Complexity.space_hierarchy` (`SpaceComplexity/Hierarchy.lean:267`), with
the corollaries `LOGSPACE_ssubset_PSPACE` (`:284`) and `SPACE_linear_ne_NP` (`:314`), one fill on
one file. **The user ruled (2026-10-27): H first, with both corollaries as later checkpoints; F6
(`space_universal`, the same file) after U2's harvest API PR.** This note maps the docstring's
sketch onto the published hosts, which have all landed since it was written, and marks where the
brief supersedes it.

**The statement** (frozen). For space-constructible `f` and `g` with
`∀ A, ∃ N, ∀ n ≥ N, A · f n ≤ g n`: `SPACE f ⊂ SPACE g`.

## Every host is proved (at the tip; `campaign/status/2026-10-27-headlines/HHosts.*`)

17 axiom prints, all on `[propext, Classical.choice, Quot.sound]` or fewer:
- **the universal machine** `Turing.exists_selfUniversal` (`TuringMachine/SelfUniversal.lean:143`):
  one `U₀` for the scheme `Complexity.TimeHierarchy.code`, with, per code `α`, a `C > 0` such that a
  halting run of `decode α` on `pairEncode α w` within space `s` is reproduced by `U₀` with the same
  output within space `C · (s + 1)`;
- **the record rows**: `exists_recordInitTM` (`Build/RecordTable.lean:5809`; the initial record of
  `Cfg.init q₀ x` at radius `s`, given `s` in binary on tape 1, time and head displacement
  `O(L + |ws| + s + 1)` with `L = recordLength`), `exists_recordTemplateTM`, `exists_recordTestTM`
  and `exists_recordStepTM` (`Build/CfgRecord`);
- **the configuration-count runner** `Turing.exists_configWindowRunnerTM`
  (`SpaceComplexity/WindowClock.lean:1506`): from a radius-`s` record of a configuration in its
  window, with the other tapes blank, it reaches an exit `out` within `C · 2^(C (L + 1))` steps, in
  space `(K + 1)(2C(L + 1) + 1)`, silently, with `out` the window run's verdict at every round count
  up to `configBound + 1` and, unless exhausted, the record of the window run's endpoint left on
  tape 0. **The clock is inside it** (F3, Route A, proved), so H builds no clock of its own;
- the window run's facts `FinTM.inWindow_of_spaceUsed_le`, `windowRun_summary_of_halts`,
  `FinTM.configBound_le_two_pow` (`WindowClock`), and `outSummary`, `outSummary_append_congr`,
  `outSummary_eq_accept_iff` (`ConfigGraph`);
- **the normal forms**: `Turing.FinTM.one_work_tape_binary_spaceUsed` (`Robustness/SingleTape`),
  `Turing.exists_codeTM` (`Encoding`), `MultiTapeTM.relabelState_runFrom_init` (`StateRenaming`);
- **the space facts**: `ComputesInTime.of_spaceUsed_le`, `MultiTapeTM.spaceUsed_mono`,
  `abs_pos_lt_card_visited`, `mem_visited_of_ne_none` (`ConfigCount`), and the readings
  `mem_SPACE_iff`, `decidesInSpace_iff`, `computesInSpace_iff`, `spaceConstructible_iff`,
  `SPACE.mono`, `SPACE.mono_const` (`SpaceComplexity/Basic`, `Constructible`).

## The shape

**The inclusion** (`SPACE f ⊆ SPACE g`): `hfg` at `A = 1` from some `N` on, `g`'s floor below `N`, and
`SPACE.mono_const`. Short.

**The diagonalizer `D`**, over the record alphabet `RecSym Q₀ (Fin 3)` (`Q₀` the states of `U₀`), on
the embedded input `x.map digitEmb`, as phases composed by the seam host (`Build/Seam`, whose
`seamCompTM_spaceUsed_le_add` and `_le_max` add the phases' spaces):
1. **Validate the input** by a fold (`Turing.inputFoldTM`, `Build/Scan`): reject at once a rich
   input that is not an embedded word. The packaging below needs `D`'s space bounded on every input
   of the rich alphabet.
2. **The radius**: run `g`'s witness, lifted to the record alphabet (`MultiTapeTM.liftSymbols`,
   `SymbolLift`), under the capture wrapper (`capture_run`, `capture_visitedByTapeHead`), writing
   `bits (g n)` on tape 1 within `O(g n)` cells. The radius is `r = g n` (`a = 1`), so the record
   initializer's radius word is the captured word itself.
3. **The initial record** of `U₀`'s start on `x` at radius `r`, with the empty-output tag
   (`exists_recordInitTM`).
4. **The run**: `exists_configWindowRunnerTM` at `U₀` with the summary update
   (`upd τ b := ` the summary of `τ` followed by `b`; `upd τ none = τ`).
5. **The verdict**: `false` if the exit is `halted` with summary `accept`, `true` otherwise.

The space: the witness's `O(g n)`, the record's `L = O(r + log n)`, the runner's `O(L)`, all `O(g n)`
by `g`'s floor, uniformly in the code part of `x`, since the window bounds the simulation. Packaging:
`decidesInSpace_of_alphabetReduction` (`ConfigCount:568`) gives a `Bool` decider of `L_D` in space
`c · (g n + 1)`, inside `SPACE g` by the floor.

**`L_D ∉ SPACE f`.** If `M` decides `L_D` in space `c₀ · f`, normalize it
(`one_work_tape_binary_spaceUsed`, `exists_codeTM`, the relabelling's space clause), take its code
`α`, and pad the payload: on `x = pairEncode α 1^N₀` with `N₀` from `hfg` at
`A := C_α (c · c₀ + c + 1)`, `U₀`'s run stays in the radius-`g n` window
(`FinTM.inWindow_of_spaceUsed_le`) and halts within `configBound` rounds, so the runner exits
`halted` with the summary of `U₀`'s output (`windowRun_summary_of_halts`), which is
`[x ∈ L_D]`; `D` answers the opposite. Contradiction.

**The corollaries.**
- `LOGSPACE ⊂ PSPACE`: `space_hierarchy` at `logSpace` and `n + 1` (both constructible,
  `spaceConstructible_logSpace`, `_linear`; `A · logSpace n ≤ n + 1` eventually), then
  `space_poly_subset_PSPACE` at degree one (`n ^ 1 + 1 = n + 1`), with `LOGSPACE_subset_PSPACE`
  (`Machines/ARMWidth:60`) for the inclusion and `LOGSPACE_eq` (`SpaceComplexity/Basic:199`) as
  `LOGSPACE`'s reading. Short; no new reading is needed (`PSPACE` is read only through these two
  inclusions).
- `SPACE (n + 1) ≠ NP`: by padding and `NP`'s downward closure under `≤ₚ` (the docstring's sketch;
  0.6–1.5k lines). Its obligations are the `NP` closure lemma, the padded language's space decider,
  the padding reduction and the strictness extraction.

## Where the brief supersedes the docstring's sketch

- **The clock** is `exists_configWindowRunnerTM`'s, not a counter loop the fill builds (the sketch's
  step (iii) predates F3).
- **The record rows** are cited through the runner, not composed round by round.
- **The witness capture** names the lift and the capture wrapper, which the sketch leaves open.

## Sizes (ESTIMATE)

| Piece | Lines |
|---|---|
| The inclusion | 50–100 |
| `D`'s phases and their composition | 600–1,200 |
| `D`'s space bound and the packaging | 400–800 |
| `L_D ∉ SPACE f`: the normalization, the window and clock argument, the contradiction | 500–1,000 |
| `LOGSPACE ⊂ PSPACE` | 50–150 |
| `SPACE (n + 1) ≠ NP` | 600–1,500 |

In all **2.2–4.7k**, the triage's 2.1–4.5k with the corollaries.

## Decisions

1. **The agent** (a separate question): the fill-agent rule suggests Codex for a first attempt.
2. **The issue's timing:** after #174 merges (H's closure excludes `NDHost`, so the order is free),
   with the pre-ship at the issue commit.
3. **`spaceConstructible_poly`'s home** (found by the pre-ship's import probe): it is in
   `Savitch.lean`, outside H's closure, and `SPACE_linear_ne_NP` needs it at degree two.

**Ruled (user, 2026-10-27):** Codex for H's fill; `spaceConstructible_poly` moves to
`Constructible.lean` by an API PR (statement unchanged; `Constructible` gains the import of
`ClassNP/Transducer`), with its gate and a replay of `Constructible`'s downstream, before H issues.
