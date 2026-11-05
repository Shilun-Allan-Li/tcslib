# External audit pack: G5's statements, two work tapes and the efficient universal machine (PR #189, a statement gate)

## Why this PR

G5 is the reduction from `k` work tapes to two (Hennie–Stearns) for binary machines, stated run
by run and with the converse. It is the input to Theorem 1.9 at `T log T` [AB09], and through
`Diagonal.lean`'s parameterization to the `f log f` time hierarchy (book-form Theorem 3.1). The U2
design probe drafted the statements (`campaign/items/u2/probes/U2DiagParam.lean.txt`). The plan is
`campaign/items/u2/G5-statements-plan.md`, with its rulings:
- (D1) `universal_TlogT` in a small sibling module;
- (D2) the image form of the per-run alphabet reduction's converse.

This PR lands G5's interface. The Hennie–Stearns simulation itself (`two_work_tapes_run`) stays
`sorry`, for a later fill.

**The PR:** #189 on `lean/g5-statements`, head `2339d2df69a02be3cf396733268e80bb0d7c8627`
(`evidence/patches/`). Against the campaign it changes six Lean files. Two are new:
`Robustness/TwoTapes.lean` and `UniversalTlogT.lean`. Four are edited: `Robustness/AlphabetReduction`,
`Codes2Tape`, `Encoding` and the facade `TuringMachine.lean`.

## What changed (verify)

| File · declaration | Change |
|---|---|
| `Robustness/AlphabetReduction` · `Turing.FinTM.alphabet_reduction_run` (new) | alphabet reduction run by run: `∃ c M', M'.k = M.k ∧ (∀ x w t, M.ComputesInTime (x.map e) (w.map e) t → M'.ComputesInTime x w (c * t)) ∧ ∀ x w, (∃ t, M'.ComputesInTime x w t) → ∃ t o, M.ComputesInTime (x.map e) o t ∧ ∀ v, o = v.map e → v = w`; **proved** from the file's private run correspondence (`arCfg_init`, `arCfg_run`, `arTM_computes`, `arBit_embed`) |
| `Robustness/TwoTapes` (new) · `Turing.FinTM.two_work_tapes_run` | `∃ M' c, M'.k = 2 ∧ (∀ x o t, M.ComputesInTime x o t → M'.ComputesInTime x o (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧ ∀ x o, (∃ t, M'.ComputesInTime x o t) → ∃ t, M.ComputesInTime x o t`, the probe's statement verbatim; **`sorry`** |
| `Robustness/TwoTapes` · `Turing.FinTM.two_work_tapes_binary` | the function-level form, `one_work_tape_binary`'s mirror; proved from the above in two lines |
| `UniversalTlogT` (new) · `Turing.universal_TlogT` | Theorem 1.9 at `T log T`, per run with the converse, over a two-tape scheme `c : EffectiveMachineCode2`; proved from `two_work_tapes_run`, `exists_code2TM` and `universalK 2 c.toK` |
| `Codes2Tape` · `Turing.exists_code2TM` (new) | every two-work-tape binary machine has a coded equivalent (the two-tape counterpart of `exists_codeTM`) |
| `Encoding` · `Turing.FinTM.computesInTime_relabelState`, `Turing.FinTM.stateEquivFin` (new) | renaming a bundled machine's states along an equivalence preserves `ComputesInTime`; a machine's states as `Fin (|State| - 1 + 1)`. `exists_codeTM_spaceUsed`'s time clause, `FinTM.toCodeTM`'s body and `toCodeTM_computesInTime_iff` now use them, and so does `exists_code2TM` (ruled by the user, 2026-11-04: the renaming argument is factored once rather than repeated) |
| `TuringMachine.lean` | imports the two new modules; their lines in the module list |

**The freeze:** every existing public statement is unchanged. The bodies change only in
`exists_codeTM_spaceUsed`, `toCodeTM` and `toCodeTM_computesInTime_iff` (`evidence/freeze/`).

## Brief for the auditor

1. **The statements.**
   - `two_work_tapes_run`: is it true as stated, for every `M`, `k = 0` and `k = 1` included?
     Is the bound `c · (t + 1)(log₂(t + 1) + 1)` the right form for the Hennie–Stearns
     simulation (`t` the source's halting time, the constant depending on `M`)? Is the converse
     what a universal machine needs?
   - `alphabet_reduction_run`'s converse, the image form (D2): `M'` decodes emitted symbols
     through a private total decoder, so only images `v.map e` determine `w`. Is the form
     adequate for G5's fill, and is anything stronger provable from the construction?
   - `universal_TlogT`: does it say Theorem 1.9 (with the relaxed code quantifier of
     `universal_quadratic`, as recorded in the module's deviations)?
2. **The proofs** of `alphabet_reduction_run`, `exists_code2TM`, the `Encoding` refactor,
   `two_work_tapes_binary` and `universal_TlogT`. Are they correct, and statement-preserving where
   they replace existing proofs? `toCodeTM`'s value changes; it has no use outside `Encoding`.
3. **Axioms** (`evidence/axioms/`):
   - `alphabet_reduction_run`, `exists_code2TM` and `computesInTime_relabelState` must be on
     `[propext, Classical.choice, Quot.sound]`;
   - `two_work_tapes_*` and `universal_TlogT` add `sorryAx`, which must come only through
     `two_work_tapes_run` (`universalK` is admission-free).
4. **Rule 10** (`evidence/rule10/`): four sealed copies (`AlphabetReduction`'s new theorem,
   `Encoding`'s relabelling section, `exists_code2TM` and `UniversalTlogT`) under a seal of 14
   definitions, with `attribute [-simp]` on three. Each copy elaborates with 0 errors; the only
   output is `Encoding`'s pre-existing `sorry`. Controls: 28 of 28 pass unsealed, and 0 of 28 pass
   sealed. Is any other-file definition unfolded or closed by reduction?
5. **Homes (D1):** `TwoTapes` beside `SingleTape`; `UniversalTlogT` as a sibling, since the
   `Robustness` layer does not import `UniversalK`. `alphabet_reduction_run` must be in
   `AlphabetReduction`, since it uses the file's private run lemmas. Its downstream is 325
   modules, the replay below.
6. **Duplication** (`evidence/screen/`): the v3 screen of 13 files, base the campaign tip
   `057da7a7` (1,004 declarations, 692 pairs), head `2339d2df` (1,010, 697): 5 new pairs, none gone
   (`pairdiff.txt`).
   - `exists_codeTM_spaceUsed` and `exists_code2TM` (94% and 73%), and `exists_code2TM` against
     `toCodeTM_computesInTime_iff` (74%). **Disposition: idiom.** After the factoring, each is a
     four-line invocation of `FinTM.computesInTime_relabelState` (with `stateEquivFin`) around its
     own code type's constructor. The renaming argument is stated once; nothing is re-derived.
     Before the factoring, the pair was 67% of a re-derived argument
     (`evidence/superseded-6bd12e68/screen/`).
   - `alphabet_reduction_run` against `Universal`'s `timedCut_live_before` (70%) and
     `timedPrefix_live` (50%). **Disposition: idiom.** The shared text is the invocation of
     `Nat.exists_eq_add_of_le`, `MultiTapeTM.runFrom_add` and `MultiTapeTM.runFrom_of_halt` (a
     halted run is stationary). No published lemma states the whole configuration's stationarity
     past a halt; `runFrom_output_eq_of_halt` states its output only.

   Does anything else re-derive existing material?
7. **Names** (`evidence/names/`): the new names on every ref.
8. **Public-facing text and lint** (`evidence/lint/`): the docstrings' sketches and references
   (`[HS66]`, `[AB09, Theorem 1.9]`).
   - **Campaign lint:** 0 FAIL / 71 WARN at base and head. One WARN line changes: `Encoding`'s
     check-8 list gains `FinTM.stateEquivFin`, an `Equiv` whose API is Mathlib's `Equiv` lemmas,
     so no own lemma is added.
   - **The policy linter:** the base's five findings on the edited files, at shifted lines, and
     none on the new files.

## Repository-side attestations (verify or challenge)

- **Compilation** (`evidence/chain/`): the change compiled with `lean -o`, in dependency order,
  into a copy-on-write clone of `oleans-larm2` (the campaign after #182). All 42 modules on the
  path to the targets and `Universal` exit 0. The only new warning is `two_work_tapes_run`'s
  `sorry`; `Encoding` keeps its one pre-existing `sorry` warning.
- **Replay:** `replay-lg5` (`evidence/merged-tree/`), the six files' downstream closure,
  325 modules, chained from `oleans-ledge` (the campaign after #184).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/92-g5-statements/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `g5-statements-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
