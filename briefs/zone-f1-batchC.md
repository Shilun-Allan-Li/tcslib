# §13 fill campaign — Tranche A-S2, Batch ZF-C: the Z4 space annotations (`Robustness/{SingleTape,AlphabetReduction}.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`.
- Create your working branch off it (suggested name `fill/zone-f1-C`),
  record the base commit hash in `REPORT.md` (the brief was issued at
  `8f13d74ecba8e73a3642d605f462774092d7ef8a`), and never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `zone-f1-C.zip` with the standard contents.

## Context

You are filling the **3 audited-true statements** of the Z4 space
annotation: `one_work_tape_spaceUsed` and `one_work_tape_binary_spaceUsed`
(`Robustness/SingleTape.lean`) and `alphabet_reduction_spaceUsed`
(`Robustness/AlphabetReduction.lean`). The statement gate closed in three
rounds (`audits/zone-infra-{,r2-,r3-}findings.md`, summary
`audits/zone-infra-resolutions.md` — read them). **The central fact of
this batch**: the round-1 audit REFUTED the received `sweepTM` as a
witness for the one-tape statement (its `.growLeft`/`.growRight` phases
extend the window unconditionally every macro-step; a stationary-work-head
input scanner has source space 1 but simulator space `Ω(n)`). The
statements are confirmed true; **your job is the demand-grown replacement
witness**. Batches ZF-A and ZF-B run concurrently — you never touch
`Build/Zone.lean` or `Codes2Tape.lean`.

## Owned files (modify these and nothing else)

`Robustness/SingleTape.lean` (2 targets) and
`Robustness/AlphabetReduction.lean` (1 target). Fill order:
`alphabet_reduction_spaceUsed` (the received `arTM` witness IS suitable
here — only its space analysis is new), then `one_work_tape_spaceUsed`
(the new witness, the batch's summit), then the composite.

## Ground rules (binding)

1. **File ownership**: only the two owned files; only the 3 targets'
   proofs plus `private` helpers; every new declaration listed (the epoch
   audit blind-restates them).
2. **Statement freeze** — in particular, the three target statements are
   exactly as audited; the existing audited one-tape/alphabet surfaces
   (`one_work_tape`, `one_work_tape_binary`, `alphabet_reduction`, their
   privates) are **untouched**.
3. **Duplication governance — this batch is explicitly screened**
   (round-1 A-S2-2's proposed fix and the round-2/3 carried dispositions):
   the demand-grown witness must **reuse and refactor the existing sweep
   infrastructure without copying it**. Private near-copies of the
   `sweepTM`/`SweepCell` machinery are exactly what the ledger now
   polices; consume the existing public/`private`-in-file material by
   citation where visible, build genuinely new control where not, and
   disclose every borderline case in the ledger line.
4. **Escalation** on anything unprovable as stated; **continuation
   budget**: deliver the alphabet target complete rather than three
   partials.

## Inherited audit contract (verbatim; binding)

The refutation (keep as a regression comment; the optional regression
lemma below is audit-adopted):

> Take a fixed Boolean machine with one work tape, whose work head never
> moves [...] source space is 1 at every horizon [but] `sweep_run_to_halt`
> places the received witness's work head, after `t` simulated steps, at
> `−t·M.k − 1` [...] at least `n + 3` distinct cells were visited,
> [contradicting] `n + 3 ≤ c(S(n) + 1) = 2c` for every `n`.

The demand-grown route (round 1, re-verified round 2):

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

The alphabet target (round 1):

> Let the fixed block width be `W = Fintype.card Γ + 1`. The received
> `arTM`'s read pass can momentarily reach the first cell immediately
> beyond the current block; that boundary must be counted. For each source
> visited interval `I_h`, all corresponding physical visits lie between
> `W·min I_h` and `W·(max I_h + 1)`, so
> `spaceUsed_arTM ≤ W·Σ|I_h| + M.k ≤ (W+1)·S(n)`, the last inequality by
> the time-zero fact `M.k ≤ S(n)`. Zero tapes: both sides zero. The
> existing fixed-length macro-cycle supplies the linear time factor. The
> hypotheses apply on `x.map e`, which has the same length as `x`.

The composite (round 1, re-verified round 2): with first-stage coefficient
`c₁` and second-stage `c₂`,

> `c₂(c₁(S(n)+1)+1) ≤ c₂(c₁+1)(S(n)+1)` and, with `Q = (T(n)+1)² ≥ 1`,
> `c₂(c₁Q+1) ≤ c₂(c₁+1)Q`. No argument compares `S(n)` with any other
> input length; no monotonicity premise is missing.

## Optional permanent lemmas (audit-adopted; flagged)

A trajectory-containment theorem for the new witness, valid inside a sweep
and on all target-alphabet inputs; **the stationary-head scanner as a
regression** showing why unconditional radius growth is forbidden.

## Environment and verification

Standard fill setup; iterate per edit on the touched file. Final, in
order: `Robustness/AlphabetReduction`, `Robustness/SingleTape` — both
**zero errors, zero sorry warnings** — then
`Robustness/Oblivious` and the `TuringMachine` facade (zero errors; the
tree's remaining sorries are ZF-A/ZF-B's concurrent surfaces and the
baseline admissions). Axiom prints for the 3 targets (at most the standard
triple, no `sorryAx`). Lint on `TCSlib/Complexity/TuringMachine` — 0 FAIL
(SingleTape's size WARN is justified in the plan's decision log; cite it).

## REPORT.md checklist

- [ ] 3/3 (or the alphabet target + frontier); base hash; every new
      `private` listed with roles; optional exports or "none".
- [ ] **Duplication ledger with the reuse-not-copy screen addressed
      explicitly**: which existing sweep material is cited, which is
      genuinely new, and any borderline disclosure.
- [ ] Final sweep tail + 3 axiom prints + lint line.
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin (hard-won)

- The existing `sweepTM` privates live in your owned `SingleTape.lean` —
  visible and citable; the refactor may generalize them **in place only
  if** the audited existing theorems' statements and proofs stay
  byte-identical (safest: new privates consuming the old ones, not edits).
- All-time bounds: every horizon `t`, including post-halt (halted
  configurations are fixed) and mid-sweep — the round-1 counterexample is
  exactly a mid-trajectory obligation; prove trajectory containment, not
  an endpoint estimate (the §12 `f2_space_of_time` lesson).
- The retraction is finite-control: never materialize the retracted
  input (an input copy is the exact cost the Ex 4.1 assessment flagged).
- `Fintype.card Γ + 1` block arithmetic: keep `W` abstract; `omega` after
  `Nat.le_mul_of_pos_left`-style facts rather than `nlinarith`.
- `Function.update_of_ne`; `dsimp only` after `cases` on control; the
  style linter requires "Proof sketch" before any sorried private in a
  partial delivery.
