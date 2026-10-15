# §13 fill campaign — Tranche A-S2, Batch ZF-C2 (continuation): the one-tape space annotation (`Robustness/SingleTape.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Create your working branch off it (suggested name `fill/zone-f1-C2`).
  Record the base commit hash in `REPORT.md`; the brief was issued at
  `f171767f32e573c345f3fa9b6e9fb87e14b84ddf`. Never rebase.
- **Delivery is by zip, not PR or push**: `zone-f1-C2.zip` with the
  standard contents.

## What this is

This is a continuation of batch ZF-C (`briefs/zone-f1-batchC.md`; read it
in full, since everything there binds unless amended here). ZF-C proved
`alphabet_reduction_spaceUsed`, which is integrated. Its report is
`audits/zone-agent-reports/f1-C-REPORT.md`; read it, especially the
continuation frontier. **Your targets are the remaining two**, in
`Robustness/SingleTape.lean`:

1. `Turing.FinTM.one_work_tape_spaceUsed`, the summit, which needs the new
   **demand-grown** sweep witness;
2. `Turing.FinTM.one_work_tape_binary_spaceUsed`, the composite, filled
   only after target 1 is closed. It may cite the now-proved
   `alphabet_reduction_spaceUsed` by its public name.

**The central fact is unchanged.** The received `sweepTM` is REFUTED as a
space witness: it grows its window unconditionally, and the
stationary-head scanner counterexample is in the target's docstring.
Never use it as the witness.

## Owned file (modify this and nothing else)

`Robustness/SingleTape.lean`: the two target proofs plus new `private`
declarations. `AlphabetReduction.lean` is closed; do not touch it. Every
existing declaration of `SingleTape.lean`, including the whole `SweepCell`
family, `sweepTM`, the audited `one_work_tape`/`one_work_tape_binary`, and
their privates, stays **byte-identical**. New material consumes the old;
the old is never edited.

## Ground rules (binding)

1. **Statement freeze.**
2. **Reuse-not-copy, explicitly screened.** This is the batch's
   duplication question, as in ZF-C's brief. Cite the received sweep
   representation and the generic `Sweep.lean` API. Build genuinely new
   control only for the demand-grown boundary logic. **Do not copy** the
   `sweep_init`/`sweep_prepare`/`sweep_finish`/`sweep_step` proof
   families. Their statements mention the old `sweepTM`, so either
   establish a restricted transition agreement for a delegated phase (the
   proved Z5 `runFrom_eq_of_agreeOn` in `Simulation.lean` is available) or
   use the generic API. The ledger line names every borderline case.
3. **Escalation** on anything unprovable as stated. **Continuation
   budget**: target 1 complete beats two partials.

## Inherited audit contract (verbatim from ZF-C's brief; binding)

> Use a sweep machine that extends a boundary only when a simulated head
> first crosses it. If `I_h` is the interval visited by source tape `h`,
> each contains 0, and therefore `|⋃ I_h| ≤ Σ |I_h| = spaceUsed_M`. A
> realization interleaving `M.k` tagged cells per coordinate pays an
> additional factor `M.k` [...] absorbed into `c`. Mid-sweep visits,
> including a boundary extension for the next simulated transition, lie in
> the representation of source-visited intervals through that transition
> plus a constant boundary allowance. Each source step still uses
> `O(t + 1)` physical steps, giving `O((T(n)+1)²)` total time.
>
> There is an additional quantifier obligation: the space conclusion
> ranges over **all** words over the enlarged alphabet `Γ'`, whereas
> correctness ranges only over `x.map e`. When `Γ` is nonempty, choose a
> finite-control retraction from `Γ'` to `Γ` that fixes `e`; simulate the
> corresponding source input without materializing a copy. Its length is
> unchanged, so `hS` applies without monotonicity. When `Γ` is empty,
> every source input and output is empty; an immediately halting
> one-work-tape machine supplies the required statement. For `M.k = 0`,
> the unused-tape embedding uses exactly one visited cell.

> [composite] `c₂(c₁(S(n)+1)+1) ≤ c₂(c₁+1)(S(n)+1)` and, with
> `Q = (T(n)+1)² ≥ 1`, `c₂(c₁Q+1) ≤ c₂(c₁+1)Q`. No argument compares
> `S(n)` with any other input length; no monotonicity premise is missing.

## ZF-C's construction plan (from its report; the route is binding, the citations are guidance)

1. Retain and cite `SweepCell`, `SweepAlphabet`, `sweepEmbed`,
   `sweepBoundary`, `sweepSymbol`, `blankRow`, `rightRow`, `headAt`,
   `tapeRow`, `tapeZone`, `readVisit`, `writeVisit`, and their facts
   `read_row`, `write_row`, `read_zone`, `write_zone`, `tapeZone_append`,
   and the length and blank-row facts.
2. Build new finite control that records boundary-head flags during the
   read sweep and decides whether the pending source action first crosses
   either boundary. **Extend only a crossed boundary.** The old
   controller is preserved unchanged.
3. Use the generic `Sweep.lean` zipper/transduction API (`sweepCfg`,
   `sweepRevCfg`, `sweep_run`, `sweep_run_reverse`, `sweep_generate`, and
   the one-cell movement lemmas).
4. Maintain a represented coordinate interval containing exactly the
   union of source-visited intervals plus the boundary cells. Prove
   containment for **every prefix of every phase**, charging a crossing to
   the current source transition, and carry post-halt absorption
   explicitly.
5. Nonempty `Γ`: a total finite-control retraction of
   `SweepAlphabet Γ M.k` to `Γ` fixing `sweepEmbed`, applied to native
   input reads and never materialized. The received `sweepInput` sends
   non-image symbols to `none`, so it is not this total retraction.
6. `M.k = 0`: cite `unusedTapeTM`, `unusedTapeCfg`, `unusedTape_step` and
   `unusedTape_computes`, and prove the stationary unused head visits
   exactly one cell. Empty `Γ`: the trivial one-tape machine that halts on
   its first transition.
7. Bound each sweep by a constant times (source step index + 1), and sum
   to the quadratic time. The old `sweepTime` formula describes
   unconditional growth and is not a timing theorem for the new machine.
8. Only after target 1: the composite, with coefficient `c₂ * (c₁ + 1)`
   for both time and space.

## Optional permanent lemmas (audit-adopted; flagged)

The new witness's trajectory-containment theorem, valid inside a sweep and
on all target-alphabet inputs, and **the stationary-head scanner as a
regression lemma** showing why unconditional growth is forbidden.

## Environment and verification

The standard fill setup; **never `lake build`**. Final checks:

- `Robustness/SingleTape` with **zero errors and zero sorry warnings**;
- `Robustness/Oblivious` and the `TuringMachine` facade with zero errors;
- axiom prints for the 3 Z4 targets, with the alphabet target re-printed,
  each at most the standard triple and no `sorryAx`;
- lint on `TCSlib/Complexity/TuringMachine`, 0 FAIL.

`SingleTape.lean` will grow well past its current 1,045 lines. Its size
WARN is justified in the plan's decision log ("A-S2 spec layer LANDED",
with the split reserved for a later window); cite it.

## REPORT.md checklist

- [ ] 2/2, or target 1 plus a frontier; base hash.
- [ ] Every new `private` listed with its role; optional exports, or
      "none".
- [ ] **The reuse-not-copy screen addressed explicitly**: which sweep
      material is cited, what is genuinely new, any agreement-transfer
      use, and any borderline case.
- [ ] Final sweep tail, 3 axiom prints, and the lint line.
- [ ] Diff touches only `Robustness/SingleTape.lean`.

## Known pitfalls at this pin (hard-won)

- **All-time bounds.** Every horizon counts, including mid-sweep and
  post-halt. The round-1 counterexample is a mid-trajectory obligation:
  prove trajectory containment, not an endpoint estimate (the §12
  `f2_space_of_time` lesson).
- **Never materialize the retracted input.** An input copy is the exact
  cost the Ex 4.1 assessment flagged.
- Z5 is **same-carrier**: transport first, then agree. Never feed
  `runFrom_eq_of_agreeOn` two machines of different tape counts or state
  types.
- `Function.update_of_ne`; `dsimp only` after `cases` on control; prefer
  `omega` after `Nat.le_mul_of_pos_left`-style facts over `nlinarith`.
- The style linter requires a literal "Proof sketch" before **every**
  `sorry`; this matters only for a partial delivery.
