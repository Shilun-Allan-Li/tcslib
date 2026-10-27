# H: the nondeterministic time hierarchy's chain, a second track (design note, maintainer, 2026-10-27)

**What this is for.** `Complexity.ntime_hierarchy` (`Diagonalization/NTimeHierarchy.lean:1723`,
H) is C1-E's third piece: "pure, from `exists_diagonalizer`, the normal form,
`NDMachineCode.decode_encode` and the stage lemmas" (`C1E-design.md`). Its file is not E-Q's or
E-D's, and it cites only their statements, so it can run **now, in parallel with E-Q**: proved
modulo E-D's `exists_diagonalizer` (and through it E-Q's `exists_queryTM`) and NF's
`exists_codeNDTM_accepts_linear`. It was waiting on UN's integration (backlog, X1); UN is
integrated: `exists_timed_universal_NDTM` and `exists_ndAcceptsWithin_decider` are proved in the
same file.

## The ingredients (all stated at #169's merged head)

- `Turing.NTimeDiag.exists_diagonalizer` (sorried, E-D): `D`, a uniform `K`, and per code `α` a
  constant `C` with the middle's soundness and completeness and the top's flip, under the
  hypothesis `hBF`.
- `hBF`: **proved here**, by `Turing.exists_ndAcceptsWithin_decider c`.
- `Turing.FinNDTM.exists_codeNDTM_accepts_linear` (sorried, NF): a coded machine `M'` and `C₁` with
  `N.AcceptsWithin x t → M'.AcceptsWithin x (C₁ (t + 1))`, and the converse at some `t'`.
- The code: `Turing.exists_effectiveNDMachineCode` and `decode_encode` give `α` with
  `c.decode α = M'`.
- The stage laws (`NTimeDiagonalizer`, proved): `stage_spec`, `ladder_succ`, `le_ladder`,
  `ladder_strictMono`, `stageCode_frequently`, `budget_eq`; `acceptLang_mem_NTIME` for
  `L(D) ∈ NTIME (g + 1)`.
- `Complexity.mem_NTIME_iff`, `NTIME.mono`, `FinNDTM.DecidesInTime`, `AcceptsWithin.mono` and
  the truncation `NDTM.runWith_of_halt` (used by `NTIME.mono`'s proof; the brief names it).

## The proof (the chain of [AB09, Figure 3.1])

**Inclusion.** `hfg` at `A = 1` gives `f n ≤ g n` for `n ≥ N₀`; below `N₀` the finitely many
lengths are absorbed into the constant (`c · f n ≤ c · F · (g n + 1)` with
`F = 1 + Σ_{n < N₀} f n`), the received `time_hierarchy` idiom. So
`NTIME f ⊆ NTIME (g + 1)`, through `mem_NTIME_iff` and the machine's own decision.

**Strictness.** Let `L = L(D)` at the budget `K · (g n + 1)`; `L ∈ NTIME (g + 1)` by
`acceptLang_mem_NTIME`. Suppose `L ∈ NTIME f`, decided by `N` within `c₀ · f`. Take `M'`, `C₁`
from NF and `α` with `c.decode α = M'`, and `C` from `exists_diagonalizer` at `α`. Choose a stage
`i` of `α` (`stageCode_frequently`) beyond three thresholds, with `a = ℓᵢ + 1`, `T* = budget f ℓᵢ`:
1. **the middle's completeness:** for `ℓᵢ < n < ℓᵢ₊₁`,
   `C · (C₁ · (c₀ · f (n + 1) + 1) + 1) ≤ g n`, from `hfg` at `A = C · C₁ · (c₀ + 1) + C + 1`
   (`n > ℓᵢ ≥ i + 2` makes `n` large);
2. **the top:** `C · 2^{C · (T* + 1)} ≤ ℓᵢ₊₁ = 2^{T*²}`, once `T*` is large;
3. **the bottom's transfer:** `C₁ · (c₀ · f a + 1) ≤ T* = (f a + a + 1)²`, once `a` is large.

Then, for every `n` in the middle (`ℓᵢ < n < ℓᵢ₊₁`, and `n ≥ 3`):
`1ⁿ ∈ L ↔ 1^{n+1} ∈ L`. Forward: the middle's soundness gives `M'` accepting `1^{n+1}` within
`g n`, NF's converse an accepting `N`-branch, and `N`'s decision (with the truncation to its
all-branch budget) `1^{n+1} ∈ L`. Backward: `N` accepts within `c₀ · f (n + 1)`, NF gives `M'`
within `t' = C₁ (c₀ f (n + 1) + 1)`, threshold 1 gives `C (t' + 1) ≤ g n`, and the middle's
completeness gives `1ⁿ ∈ L`. By induction from `a` up to `ℓᵢ₊₁`: `1^a ∈ L ↔ 1^{ℓᵢ₊₁} ∈ L`. The
top's flip (threshold 2) gives `1^{ℓᵢ₊₁} ∈ L ↔ ¬ M'` accepts `1^a` within `T*`, and the bottom's
transfer (threshold 3, `AcceptsWithin.mono`, NF's converse, `N`'s decision) gives
`M'` accepts `1^a` within `T*` iff `1^a ∈ L`. So `1^a ∈ L ↔ ¬ 1^a ∈ L`: a contradiction.

**Sizes (ESTIMATE):** 800–1,500 lines. About a third is the thresholds' arithmetic, through
`hfg` and the ladder's laws. Then the chain induction (about 200 lines), and the inclusion with its
finite absorption (about 200 lines). No machine is built.

**The docstring.** `ntime_hierarchy`'s sketch still describes the older construction inline: the
locator, the guess, the self-clocked mid-rung and the prefix clause. The C1-E statement phase
moved all of that into `exists_diagonalizer`. The X1 patch (`x1-ntimehierarchy-docstring.patch`)
updated only the nominal budget. A fill cannot edit the docstring before its own region (d), so
the brief must say which parts are superseded. The maintainer rewrites the sketch at integration
to "the chain over `exists_diagonalizer`".

## Hazards

- `Complexity.time_hierarchy`'s and `space_hierarchy`'s finite-absorption idioms: cite a published
  form if one exists (the brief's pre-ship searches); otherwise a private lemma, disclosed.
- NTIME's truncation inside `NTIME.mono`'s proof (private steps there): cite
  `NDTM.runWith_of_halt` and `runWith_append`, never re-walk `NTIME.mono`.
- UN's own lemmas in the file (`un_`): unrelated, but in the same file; no new `un_` names.

## Decisions

1. **When H runs.** (a) **Now, as a second track in parallel with E-Q** (recommended). It is a
   different file, cites only statements, and adds no machine. The cost is that it lands "proved
   modulo E-D and NF", and its axiom walk shows their `sorryAx` until they land. (b) After E-D:
   H becomes admission-free once NF lands, but it waits behind E-Q and E-D.
2. **The docstring.** (a) **The brief marks the old sketch as superseded, and the maintainer
   rewrites it at integration** (recommended; no extra PR). (b) A docstring-only PR first
   (X1, rewritten to the chain): one more merge before the brief issues.
3. **The agent:** Codex (a first attempt, by the agent rule), alone in a small megafill, or with
   another ready item.
