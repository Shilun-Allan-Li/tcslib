# Absorbing-stop first entry: unapproved proposal probe

2026-11-07. **UNAPPROVED — proposal evidence only, no implementation or T2 closure.**
The proposed generic theorem and four sealed hypothetical consumer shapes passed actual
elaboration. It still needs Seyoon's ruling before publication in the library.

Proposed name: `Turing.MultiTapeTM.exists_first_entry_of_fixed`.
Proposed home: `TuringMachine/Finite.lean`, beside `exists_first_halt`. No new import,
definition, state/table change, or additional public lemma is proposed.

```lean
theorem exists_first_entry_of_fixed {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (stop : State → Prop) (c d : Cfg k Symbol State input) (T : ℕ)
    (hfix : ∀ z : Cfg k Symbol State input,
      (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q)
    (hT : tm.runFrom c T = d) :
    ∃ t ≤ T,
      (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d
```

This is the existing two private lemmas' mathematical contract, generalized only from Bool
to an arbitrary alphabet. There is no `DecidablePred stop` premise: the proof chooses the
least hit classically. It preserves the complete endpoint configuration and the strict
pre-entry cut. Time zero remains allowed; positivity stays a caller obligation. No
finiteness, extra liveness, or state-only substitute for whole-configuration fixedness is
assumed.

The proof uses `Nat.find_spec`, `find_min`, `find_min'`; a local fixed-run induction through
published `runFrom_zero`/`runFrom_succ_eq_step`; then `runFrom_add`. It never converts
`runFrom` definitionally to `Function.iterate`, never passes a Core/Mathlib definition as a
tactic argument, and introduces no public fixed-run helper. The actual proof is archived in
`Proposed-contract.lean.txt`.

## Executed results

Every completed run used the plain managed `leanelab.sh`, full **oleans-mac3**, one Lean
process at a time, local shared-slot budget three, no nested lock and no compiled output.
The snapshot adoption receipt identifies campaign
`e3adffac67377a8b6e23bed74bfdbb44a123dd86`. Source/object hashes, actual commands,
timings and toolchain are in `context.json` and the per-run receipts.

| Probe | Actual Lean exit/errors | Scope |
| --- | --- | --- |
| `Owner-home-v1` | 0 / 0 | Exact Finite source prefix through `exists_first_halt`, followed by the proposed theorem at that insertion point. Existing imports only. `runFrom` and `step` sealed before the new theorem header. |
| `Consumers-v1` | 0 / 0 | Proposed theorem plus both old private-signature shapes, a singleton stop, and the comparator's `Fin 3 × Bool` stop predicate; both definitions sealed before every header. |
| `Controls-unsealed-v2` | 0 / 0 | Eight direct-definition delta/equation controls, pointwise and abstracted. |
| `Controls-sealed-v2` | 1 / 8 | Exactly one expected reflexivity failure per example; no stray/other errors. |

The proposed theorem in the owner and consumer contexts, and all four consumer theorems,
print only `propext`, `Classical.choice`, `Quot.sound`. No custom axiom or `sorryAx` occurs.
The unchanged owner prefix emits two existing unused-simp warnings; the positive controls
emit one unused-State-binder warning. These are retained, not suppressed.

The two signature consumers specialize the generic theorem to the unchanged Bool/private
contracts, including their old instance context. The singleton and comparator consumers
exercise the actual stopping-predicate shapes used by Loop's cleanup and Primitives'
comparison. They are **hypothetical consumers**: actual private machine witnesses and all
five call sites have not been re-elaborated or rewritten. Full Finite after the insertion
point, the MIG-1 fill tree, downstream integration, and a gate/replay are outside this probe.

## Seal and receipt checks

`runFrom` and `step` are the reached ordinary foreign TCSlib definitions. Their definition
declarations carry no definition-level simp attribute here; the proof rewrites only their
published equations. Configuration fields are projections. No TCSlib abbreviation is read
in the proposed argument.

Each sealed definition has a delta and a complete equation, each pointwise and abstracted:
step-at-halt/step-match, and zero-run/run-as-iteration. The final step-match controls use an
abstract State type. The v1 Unit-specialized complete-step equations failed even unsealed;
that unsuccessful positive attempt and the compiled-definition inspection are retained in
`Controls-unsealed.out` and `Inspect-step.out`. The unexecuted v1 negative source is
superseded explicitly, not represented as a run.

`check-results.py` verifies input/output hashes, axiom lists, eight examples and exact error
multiplicity. Its offline duplicate/missing/zero-exit checker controls are all rejected.
Those modified transcripts are synthetic checker tests, not further Lean runs. The four
recorded source files and four compiled snapshot modules have unchanged hashes after the
probe. `results.json`, raw `.out`, `.lean.txt`, `*-run.json`, and `SHA256SUMS` retain the evidence.

An initial sandboxed wrapper invocation was interrupted while waiting with no completed
Lean output/receipt; it is not counted as a successful elaboration. Subsequent invocations
had access to the managed lock directory and used normal slot acquisition. See
`execution-notes.md` for that attempt and the corrected positive controls.

## Remaining decision

The separate [source assessment](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/first-entry-assessment/README.md)
records the missing current interface and acknowledgment boundaries. This probe changes
the validation status of the proposal, not its approval status. Publishing it, choosing its
final name/home, re-pointing/removing the two private implementations, or deferring their
assigned factoring still requires the appropriate maintainer/user decision. No retained
debt is acknowledged here.

No repository source, Git state, compiled snapshot/cache, or screen was changed. Archived
sources were copied only to unique `/private/tmp/tcslib-first-entry-*/*.lean` inputs for the
managed plain elaborator. This proposal folder is the only records output.
