# MIG-24 T2: fixed-stop first-entry assessment

2026-11-07; source-only review by Codex. **The shared public contract is missing from the
inspected API; the factoring leaf remains incomplete.** This is an unapproved proposal,
**not pre-shipped**. No API, source, debt acknowledgment, or gate status is changed here.

Inspected the API worktree supplied by the maintainer as
`1160c18f03fd318f0dec25738790935fa61379d4`, at
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-natbits`, and cp07's
extracted sources. No Git command was used to resolve or verify that worktree identifier.

## The retained argument

cp07 [Loop:3641](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoint07-2026-11-07/extracted/fill-mig1-mega-cp07/source/TCSlib/Complexity/TuringMachine/Build/Loop.lean.txt:3641)
(`emCall_first_entry`) and
[Primitives:5723](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoint07-2026-11-07/extracted/fill-mig1-mega-cp07/source/TCSlib/Complexity/TuringMachine/Build/Primitives.lean.txt:5723)
(`emitter_first_entry`) have the same generic statement and proof modulo their names:
if every configuration in a designated live stopping state is fixed by `step`, and a known
bounded run ends in one of those states, its first stopping-state visit has the complete
known endpoint already. They have two Loop callers and three Primitives callers.

The endpoint is `some q` satisfying a state predicate, **not** the halting state `none`.
Fixing just the control state would not suffice: work tapes, head positions, input position
and output must also stop changing. Time zero is allowed by the generic lemma; callers
prove positivity separately from their initial-state facts.

## Existing results: components, not the missing contract

- Public `MultiTapeTM.exists_first_halt`,
  [Finite:218](/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-natbits/TCSlib/Complexity/TuringMachine/Finite.lean:218),
  requires the endpoint's state to be `none`. It does not accept these live, absorbing
  return states. Using it through a newly stopped machine would require an additional
  adapter/correspondence argument and is broader than sharing the existing fact.
- Mathlib `Nat.find_spec`, `find_min`, `find_min'` supply least-hit existence/minimality/bounds;
  `Function.iterate_fixed` supplies stationarity from a fixed configuration. **Both current
  copies already use these results**, together with `runFrom_add`. Citing those ingredients
  again does not remove their duplicated assembly.
- The public seam first-return theorems describe their constructed release/composition
  hosts, not an arbitrary `tm` under this fixed-stop premise. No matching general contract
  was found in the inspected current Finite/CfgFacts/contract/seam APIs or Mathlib's
  iterate/find interfaces. This is a bounded source search, not a theorem proving absence
  from every library.
- Private `Primitives.catalogFirstEntry` is the related one-stopping-state case. It is not
  a published cross-file interface; it cannot be cited from Loop. The historical inventory
  itself calls `emitter_first_entry` its in-file generalization with no public §12 equivalent
  (`inventory/primitives.md:164`).

## Minimal candidate contract and home

Suggested existing home: **`TuringMachine/Finite.lean`, namespace `Turing.MultiTapeTM`,
beside `exists_first_halt`**. It already owns the corresponding general run facts and uses
`Nat.find`; its existing imports supply the ingredients. Both consumers already reach
Finite. No new file or import is needed. Editing its public surface still requires Seyoon's
approval.

The narrowly scoped Bool statement matching both consumers is:

```lean
-- Proposed only, in namespace Turing.MultiTapeTM
theorem exists_first_entry_of_fixed {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (stop : S → Prop)
    (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w,
      (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q)
    (hT : tm.runFrom c T = d) :
    ∃ t ≤ T,
      (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d
```

No `DecidablePred stop`, finiteness, positive duration, or extra liveness premise is logically
needed: a classical proof supplies the decision procedure locally. Generalizing Bool to an
arbitrary alphabet is optional further scope, not presumed approved here.

For a future proof, choose the least stop using the published `Nat.find` API. Prove its
remaining run constant by a **local induction using `runFrom_zero` and
`runFrom_succ_eq_step` plus `hfix`**, then identify endpoints with `runFrom_add`.
This avoids relying on the implicit foreign-definition conversion from `runFrom` to
`Function.iterate` in the current `Function.iterate_fixed` line. It needs no additional
public fixed-run theorem. Future checks must elaborate the exact home-context proof and
both consumers with `step`/`runFrom` sealed, run the required controls, and walk axioms.
None was run for this proposal.

## What the records do and do not authorize

The duplication is **already recorded and assigned**, not newly unnoticed:

- The ledger's historical Primitives census explicitly includes `emitter_first_entry`
  among source-side correspondences to Catalog (`duplication-ledger.md:39`); D-R2's
  acknowledgment concerns that expanded Catalog correspondence inventory.
- [MIG-24 TRIAGE:38](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/items/mig24/TRIAGE.md:38)
  explicitly names the Loop/Primitives pair as a 100% rename-mirror in T2. The user answer
  below that table folds T1–T6/T2b into MIG-1's batches.
- The current fill brief explicitly assigns T2 and says that a needed new public interface
  must be reported precisely and **the family left incomplete**; it does not authorize new
  debt (`megafill-mig1.md:136–144`).

**No explicit by-kind ruling was found authorizing retention of this Loop↔Primitives
fixed-stop duplicate after its assigned MIG-1 factoring window.** The historical source-side
census and scheduling decision should be preserved, but they are not a blanket retained-debt
exception. Retiring Catalog's counterpart does not merge the two remaining proof homes.
The recently accepted SAT/Hardness adapter/dispatcher kinds concern different operations and
do not supply this permission either.

Recording a paused design leaf and incomplete T2 family is therefore supported; calling the
family discharged or accepted as retained final debt is not. Any postponement beyond that
window, or publication of the proposed interface, needs an explicit future ruling. This
assessment supplies neither.

Only this README was written. No Lean, Git, source changes, screens, cache operations,
delivered-script execution, or changes to the stable gate-106 review were performed.
