# RAM machines on Turing machines: planning note (2026-11-17)

**Ruling (Seyoon, 2026-11-17):** "all I wanted was to prove the 14 pending admissions for now".
The scope is **route C** below: prove stage 2's 14 admitted declarations, whose statements were
gated on 2026-10-14. Routes A, B and D (the book's RAM TM, a single-tape target) are not pursued
for now; §2–§5 keep the analysis for later. This work goes on a future branch into `main` and
must not delay the closeout's integration.

## 0. The work: 14 admitted declarations in three tiers

| Tier | File | Declarations | Nature | Size estimate |
|---|---|---|---|---|
| 1 | `RAMSimulation/WordSize` (3) | `WordSizeComputable.mono`, `wordSizeComputable_logSpace`, `wordSizeComputable_of_spaceConstructible` | small: monotonicity; machines for `bits(c·logSpace n)` and `bits(c·S n)` from existing length and constructibility rows | 100–300 lines |
| 2 | `RAMSimulation/Simulation` (2) | `exists_simulation`, `exists_ndSimulation` | **the main work**: a phase host over `P`'s positions with one framed contract per instruction kind (find-by-key in the (address, word) table, two-tape add and subtract mod `2^W`, shift-and-add multiply, sign test, `half`, overwrite or append an entry, input seek, output append, and `coin` as a choice step), a start-up (word size, ruler, length copy, `initMem`), and the simulation induction over `XStepsIn` | several thousand lines; several fills |
| 3 | `RAMSimulation/Classes` (9) | `mem_DTIME_of_decides`, `mem_P_of_decides`, `mem_P_of_decides_logWord`, `mem_SPACE_of_decides`, `mem_LOGSPACE_of_decides`, `computesInSpace_of_computes`, `mem_SPACE_mul_of_decides`, `mem_NSPACE_of_accepts`, `mem_NL_of_accepts` | corollaries of tier 2 and tier 1 plus bound arithmetic; can be proved first against tier 2's statements | 300–800 lines |

**Order.**
1. **Re-check the statements** against today's library. They were gated before MIG-1, R4 and the
   closeout. Check that every name cited in the proof sketches still exists with the cited
   contract; `phaseHostTM`, `exists_inputSeekTM`, `exists_inputLengthTM`, `embedSilentTM` and
   `Contract` do.
2. **Tiers 1 and 3**, while tier 2 is still admitted. Tier 3 only cites tier 2's statements.
3. **Tier 2**, in fills: the start-up, the instruction rows (grouped), the table invariant and
   the simulation induction, then the nondeterministic variant.

**Base.** The proofs should use the campaign's machine library (`Build/*`, the contracts, the
seams), which reaches `main` with W7. Two options: branch from the campaign tip now and rebase
onto `main` after W7, or start after W7 from `main`.

## 1. What was deferred, and what exists

- **The deferral.** The chapter 1 plan (`campaign/design/plans/AroraBarakChapter1Plan.md` §5 and
  its decision log) put "the RAM-TM exercise (Ex 1.9)" in Phase 5, "deferred to a much later
  effort". The backlog repeats it ("Phase 5, deliberately unscheduled").
- **The book's exercise** ([AB09], Exercise 1.9, p. 35), as I recall it; the wording needs checking
  against the 2009 text. A *RAM Turing machine* has an infinite array `A`, one work tape
  designated as the address tape, two symbols `R` and `W`, and a state `q_access`. On entering
  `q_access`:
  - with `⌞i⌟ R` on the address tape, `A[i]` is written next to the `R`;
  - with `⌞i⌟ W σ` on the address tape, `A[i]` is set to `σ`.

  The exercise: if `f` is computable within time `T(n)` (time-constructible) by a RAM TM, then
  `f ∈ DTIME(T(n)²)`. AB09's `DTIME` is multi-tape.
- **Already in TCSlib (from `main`):**
  - **The word RAM's "stage 2"** (`TCSlib/Complexity/RAMSimulation/`; design §15a–§16b; backlog
    PROG-4). [AFM26]'s word RAM, extended with `rdIn`, `emit`, `coin` and `half`, is simulated by a
    multi-tape `FinTM Bool` within `TW n + A·(t+1)·(f·(W+1) + W² + n + 1)` steps.
    - The statements were gated on 2026-10-14 and the proofs are pending: 14 admissions
      (`Simulation` 2, `Classes` 9, `WordSize` 3).
    - The deterministic statement cites [AB09, Exercise 1.9] as its source, with documented
      deviations: a word RAM rather than the book's RAM TM, and an explicit bound rather than
      `T(n)²`.
  - **Single tape:** `Turing.FinTM.one_work_tape_binary` (`Robustness/SingleTape`), [AB09]
    Claims 1.5 and 1.6. A `FinTM Bool` computing `f` within `T` gives a one-work-tape
    `FinTM Bool` within `c·(T n + 1)²`. It is proved, with standard axioms.

## 2. The bound: what is true, and where "quadratic" can fail

The obvious construction stores the array as a list of `(address, symbol)` pairs on a work tape
and scans it at each access. Its cost depends on how long addresses can get:

- **In the book's model, addresses are cheap to make long.** After writing one address of length
  `ℓ`, flipping its last bit gives a new address of length `ℓ` in `O(1)` steps. So `T` steps can
  create about `T` distinct addresses of length about `T`, and the list grows to about `T²`
  cells. One access then costs `Θ(T²)` steps, and the naive total is **`T³`, not `T²`**. I have
  not found the argument that gives `T²` in this model, and there may be a better data structure.
  **This needs settling before any statement is gated.**
- **Log-cost models give `T²`.** If an access to address `i` is charged `|⌞i⌟|` steps, as in the
  word RAM where addresses are words of `W` bits, the list has total length `O(T)`, so an access
  costs `O(T)` and the total is `O(T²)` on a multi-tape machine. Stage 2's bound is of this kind.
- **Single tape adds a square on top.** Composing any multi-tape bound `B` with
  `one_work_tape_binary` gives `c·(B + 1)²`. So:
  - "RAM to single tape in quadratic time" via the multi-tape route is **quartic in `T`** for a
    `T²` multi-tape simulation;
  - it is quadratic only in the multi-tape bound `B`.

  A direct single-tape construction in `O(T²)` would be a new result rather than the book's; I
  have not checked whether it holds for either model.

## 3. Route options

| Route | Model | Target | Bound | Work |
|---|---|---|---|---|
| **A** | Book's RAM TM (new definition) | multi-tape `FinTM` (`DTIME`) | `T²` if §2's question resolves; else `T³` honestly | new model and semantics; list-store simulation; Claim-style ledger |
| **B** | Book's RAM TM | one work tape | `c·(B + 1)²`, with `B` route A's bound | route A, then `one_work_tape_binary` (proved) |
| **C** | The word RAM (stage 2) | multi-tape | stage 2's explicit bound | prove the 14 pending admissions; the statements already exist |
| **D** | The word RAM | one work tape | `c·(simTime + 1)²` | route C, then `one_work_tape_binary`; a short corollary |

**Recommendation, pending §4.** D is the smallest new surface: route C's statements are already
gated, and D is a short corollary of C and the proved single-tape theorem. It gives a single-tape
machine whose overhead is quadratic in the multi-tape simulation's time. If the goal is the
book's exercise itself, A and B need §2's question settled first.

## 4. Decisions for Seyoon (answered for now: route C, the 14 admissions)

1. **The model:** the book's RAM TM (A, B), [AFM26]'s word RAM (C, D), or both.
2. **The target:** multi-tape (`DTIME`, as in the book), a single work tape, or both.
3. **The bound:** in "quadratic overhead", quadratic in what? The RAM's step count `T` (needs §2
   resolved for the book's model), or the multi-tape simulation's time (route D)? Should a `T³`
   statement be acceptable for the book's model if `T²` does not hold there?
4. **The relation to stage 2:** should this branch also prove stage 2's 14 pending admissions, or
   are they someone else's work on `main`? Their author and status should be confirmed first.

## 5. Draft statement shapes (unchecked; for discussion only)

**Route D**, a corollary of stage 2's deterministic form:

```lean
/-- Stage 2 on one work tape: a word-RAM program is simulated by a single-work-tape binary
machine with quadratic overhead in stage 2's time bound. [AB09, Exercise 1.9 with Claims 1.5 and
1.6] -/
theorem WordRAM.exists_oneTape_simulation (P : XProgram) (fn : Bool) {W TW SW T F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hP : ∀ x, ∃ v o, HaltsWithin P x [] (W x.length) (T x.length) v o (F x.length))
    (g : List Bool → List Bool)
    (hg : ∀ x v o, HaltsWithin P x [] (W x.length) (T x.length) v o (F x.length) →
      g x = outputOf fn v o) :
    ∃ (M : Turing.FinTM Bool) (A c : ℕ), M.k = 1 ∧
      M.ComputesFunInTime g fun n => c * (simTime A TW n (W n) (T n) (F n) + 1) ^ 2
```

Its proof would be `exists_simulation`, then `computesFunInTime_iff`, then
`one_work_tape_binary`, with monotonicity of `simTime` in `t` and `f`. One check is still open:
`ComputesFunInTime` needs one bound per input length, so `hP` and `hg` take `T` and `F` as
functions of `|x|`.

**Route A**, the book's model. The new definitions would be:
- `Turing.RAMTM`, a `MultiTapeTM` with a designated address tape, `R`/`W` symbols and an access
  state;
- its configuration, which adds the array `ℕ → Option Γ`;
- its step and `ComputesInTime`.

The theorem:

```lean
/-- [AB09, Exercise 1.9]. -/
theorem Turing.RAMTM.mem_DTIME_sq {T : ℕ → ℕ} (hT : TimeConstructible T) (M : RAMTM …)
    (f : List Bool → List Bool) (hM : M.ComputesFunInTime f T) :
    ∃ M' : FinTM Bool, ∃ c, M'.ComputesFunInTime f fun n => c * (T n + 1) ^ 2
```

This is only true if §2's question resolves in favor of `T²`. Otherwise the exponent is 3, or
the model charges an access by its address length.

## 6. Next steps once §4 is decided

1. Check Exercise 1.9's wording against the 2009 text (route A or B).
2. Settle §2: find or rule out a `T²` argument for the book's model.
3. Write the statement file on a new branch from `main`, after the closeout's W7 merges, then a
   statement gate.
4. Plan the fills; for route D, a single maintainer PR.
