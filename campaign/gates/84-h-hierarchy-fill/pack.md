# External audit pack — H, the nondeterministic time hierarchy (PR #172, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09,
Theorem 3.2]). The target is `Complexity.ntime_hierarchy` in
`TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean`, proved from two contracts that stay
`sorry`: the diagonalizer `Turing.NTimeDiag.exists_diagonalizer` (`NTimeDiagonalizer`) and the
linear coded normal form `Turing.FinNDTM.exists_codeNDTM_accepts_linear` (`NDNormalForm`).

- **The brief:** `campaign/fills/h/drafts/h-fill-hierarchy.DRAFT.md`, with its route note
  `campaign/items/c1/c1e/H-route-design.md`. It was never issued.
- **The proof:** assembled by the review of that brief (`campaign/fills/h/reviews/brief/REVIEW.md`;
  the chain probe `probe/HChainProbe.lean.txt`, filled in place as
  `probe/NTimeHierarchyFilledA.lean.txt`). The review's major F1 found that the truncation of an
  unbounded acceptance had no licensed host.
- **The user's rulings (2026-10-27):** D1 (A), a second import, `TuringMachine/ChoiceWords`, with
  the truncation through `Turing.run_take_of_halted`; D2, land the review's proof by a maintainer
  PR with a fill gate and the downstream replay.

**The landing:** PR #172 on `lean/h-hierarchy-landing`, head
`33d685374abb27bb6106853c0026920f52bd4107`, one commit on the campaign tip
`52b7edbaac3006b36fdf7443b89ac31f5e7201f8`, whose Lean is the tree after #170
(`evidence/patches/landing.patch`). It is the review's filled file with these changes:
- the review's axiom prints, its sorry walk and its section header removed;
- proof sketches added to the private lemmas;
- a private `nh_fold` (a constant factor folded into the NTIME constant), cited by `nh_inclusion`
  and by `ntime_hierarchy_of_pos`. The two had the same five-line fold; the before-screen paired
  them at 56%;
- the target's docstring rewritten, the module's status paragraph updated, and "spec, fill
  pending" removed from the two corollaries' docstrings.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target proved** | `Complexity.ntime_hierarchy`: `sorry` → lazy diagonalization over the two contracts |
| **Privates** | 10 → 20: `nh_chain`, `nh_absorb`, `nh_fold`, `nh_inclusion`, `nh_top`, `nh_bottom`, `nh_middle`, `nh_stage`, `nh_accepts_of_halts`, `nh_mem_of_accepts`, at the home before the target |
| **Changed body** | `Complexity.ntime_hierarchy_of_pos`: its factor-2 fold cites `nh_fold` (statement unchanged) |
| **Frozen** | every public statement (5 → 5); `NTIME_linear_ssubset_square`'s code (its docstring only changes: `evidence/freeze-note.txt`, since `declfreeze.py` counts a docstring edit as a body change) |
| **Imports** | `Diagonalization/NTimeDiagonalizer` and `TuringMachine/ChoiceWords` added |
| **Text** | the target's docstring (sketch and `**Implementation.**`); the module's status paragraph; the corollaries' headers |

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen statement? In particular:
   - the inclusion `NTIME f ⊆ NTIME (g + 1)` from the hypothesis at `A = 1`, with no
     monotonicity of `f`;
   - the stage's choice: one stage `i` of the alleged decider's code whose bottom rung is beyond
     `N₁ + T₀ + C₁ (c₀ + 1)`. Is each threshold used where it is needed?
   - the edge cases: `ℓᵢ ≥ 2`, the stage law at `n = ℓᵢ₊₁` (`stage_eq` with `le_rfl`), and the
     empty middle when `ℓᵢ₊₁ = ℓᵢ + 1`.
2. **The route against the contracts.** Read `exists_diagonalizer` and
   `exists_codeNDTM_accepts_linear` as stated.
   - **Middle:** soundness gives `M'`'s acceptance within `g n`, and the back transfer and the
     truncation give `1ⁿ⁺¹ ∈ L`. Completeness needs `C (t' + 1) ≤ g n` at
     `t' = C₁ (c₀ · f (n + 1) + 1)`, from `nh_middle`.
   - **Top:** the flip's threshold `C · 2^{C (T* + 1)} ≤ ℓᵢ₊₁ = 2^{T*²}`, from `nh_top` and
     `ladder_succ`.
   - **Bottom:** the forward transfer within `T*` (`nh_bottom`), and the back transfer.

   Is any hypothesis of a contract strengthened or left undischarged?
3. **The truncation** (`nh_accepts_of_halts`). Is it correct through `run_take_of_halted`, with
   absorption by `NDTM.runWith_append` and `NDTM.runWith_of_halt`? Is `nh_mem_of_accepts` the
   right reading of `FinNDTM.DecidesInTime`?
4. **Rule 10** (with the scope of 2026-10-23). The sealed copy (`evidence/NTimeHierarchySealed.*`)
   seals the review's 12 definitions: `NTIME`, `FinNDTM.DecidesInTime`, `FinNDTM.AcceptsWithin`,
   `NDTM.HaltsWithin`, `NDTM.runWith`, `NDTM.initCfg`, `NTimeDiag.ladder`, `NTimeDiag.budget`,
   `NTimeDiag.stage`, `NTimeDiag.stageCode`, `TimeConstructible` and `CodeNDTM.toFinNDTM`. It also
   erases the four `@[simp]` TCSlib definitions. The module then has 0 diagnostics.
   - The 12 controls are the review's: 4 in `HSealControl.lean.txt` and 8 in
     `HReviewSealControl.lean.txt` (`campaign/fills/h/reviews/brief/probe/`). Each closes unsealed
     and fails sealed (the review's `out/`).
   - Every `simp` is `simp only` with lemmas.
   - One `change` restates membership in the local set-builder `L` (Mathlib's `Set`), and one
     `rfl` closes a local equation.

   Does any step close only because another file's definition reduces?
5. **Duplication.**
   - **The text screen** over the review's 14-file population (`evidence/screen/`; base at the
     tip, head at `33d68537`): 224 → 226 pairs, none gone. The two new pairs:
     - `nh_accepts_of_halts` reproduces `Nondeterminism`'s private `acceptsWithin_iff_of_halts`
       at 61%. They state the same fact, and both prove it through `run_take_of_halted`. With
       `ExhaustiveReplay`'s `xr_accepts_iff_of_halts`, that makes three private statements of
       the truncation. It is disclosed and ledgered (`campaign/duplication-ledger.md`) as a
       promotion candidate for the dedup window. The user's D1 (A) licensed the leaf.
     - `nh_fold` reproduces `nh_mem_of_accepts` at 50% (61 characters, the `decidesInTime_iff`
       idiom).
   - **Semantic:** do the `nh_` lemmas re-derive published API (`NTIME.mono`,
     `AcceptsWithin.mono`, the ladder's laws)? Is `nh_fold` a re-derivation of a published lemma?
     The maintainer found none in `ClassNP/NTIME`.
   - Is the refactor of `ntime_hierarchy_of_pos` (its fold through `nh_fold`) acceptable in this
     PR?
6. **The maintainer's text.** Is the rewritten sketch an exact reading of the proof, and is the
   status paragraph true? The text must be public-facing: no campaign labels, paths or dates in
   new text. The module docstring's older campaign references ("decision CH34-Q8", "round-1
   finding 7", the plan's phase) predate this PR and are in the deferred docstring cleanup.
7. **Records.** Any correctness gap in the review's minors F2–F10, which concern the brief that
   was not issued, as they bear on this landing.

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lb5am`, the snapshot of #170's head (its tree differs from the
  tip only in `Relativization`'s docstring, outside `NTimeHierarchy`'s closure):
  - the head's `NTimeHierarchy`, with the three axiom prints and the review's sorry walk appended
    (`evidence/NTimeHierarchyAx.*`): 0 diagnostics. All three results are on
    `[propext, sorryAx, Classical.choice, Quot.sound]`, and the walk finds `sorryAx` directly
    only in `exists_codeNDTM_accepts_linear` and `exists_diagonalizer`;
  - the ten privates (`evidence/NTimeHierarchyAxPriv.*`): all within the standard three, and
    five of them on `[propext, Quot.sound]`;
  - the sealed copy: 0 diagnostics.
- **Freeze** (`evidence/freeze-NTimeHierarchy.txt`, `declfreeze.py` v4): 5 → 5 public, 10 → 20
  private, no statement changed. It lists three body changes: the target, `ntime_hierarchy_of_pos`
  and `NTIME_linear_ssubset_square`, the last a docstring change only (`freeze-note.txt`).
- **Lint:**
  - `Diagonalization` 0 FAIL, 2 WARN over 5 files, the base's warnings
    (`lint-head-Diagonalization.txt`, `lint-base-Diagonalization-warn.txt`); `NTimeHierarchy`'s
    size line goes 1,793 → 1,940;
  - the policy linter `scripts/style_lint.py`: the same 4 findings at the base and the head, all
    pre-existing (`style-lint-NTimeHierarchy*.txt`);
  - no line over 100 characters.
- **Replay:** `NTimeHierarchy`'s downstream closure (itself and the `Diagonalization` facade),
  written after #171 and E-Q's checkpoint 1 merge, since `NTimeHierarchy` imports both `TMSAT`
  (#171) and `NTimeDiagonalizer` (the landing). **Pending.**

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/84-h-hierarchy-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `h-hierarchy-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
