# Fill campaign — Epoch 3, Batch C: the oblivious simulation

## Context

You are filling one Lean 4 proof in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1:
`Complexity.oblivious_of_mem_DTIME` — [AB09, Exercise 1.5], first assertion:
for time-constructible `T`, every language in `DTIME T` is decided by an
*oblivious* machine (head positions a function of input length and time only)
within `c · (T n + 1)²`. Seventeen of the 21 audited sorries are proved;
this is one of the last four. Fair warning on its history: the phase-2 audit
**refuted the first sketch** of this construction (composing quadratic
simulations per step gives a quartic; running the constructibility witness
verbatim need not be oblivious; the real input head must be parked), and the
current docstring sketch is the audit-corrected design — treat its five
steps as binding, and read the two additional obligations below.

## The two epoch-2 audit obligations (finding 9, binding)

1. **Early halting must not stop the schedule.** `Oblivious` quantifies over
   *all* times `t` and *all* inputs of a length — if the simulated decider
   halts early on some inputs, your machine must keep executing the identical
   prescribed physical schedule (idle sweeps) for the full `B n` macrosteps
   and halt at the fixed final time. A machine whose halting time depends on
   the input's acceptance is not oblivious in this definition's sense (heads
   frozen by halting at different times on same-length inputs would still
   agree only if the halted positions happen to coincide — do not rely on
   that; run the full schedule).
2. **Fixed-duration coding needs its own trajectory argument.** Do not appeal
   to the existential `alphabet_reduction` (its witness machine makes
   data-dependent moves); the sketch's "fixed-duration binary block coding"
   means your own layout in which every read/write of a logical cell costs
   the same fixed number of physical steps regardless of contents. The
   obliviousness proof is a *trajectory* invariant — same positions on any
   two same-length inputs at every `t` — proved by induction on the schedule,
   with data affecting only tape contents, simulated state, and markers,
   never positions or durations.

Also note from the audit: `one_work_tape` (proved) does **not** give
obliviousness — its sweep extent depends on the visited zone, not on `n` and
`t` alone. Its *techniques* (and the public `Sweep.lean` layer) are reusable;
its theorem is not.

## The construction (the audited five-step sketch in `Oblivious.lean`)

Take a decider for `L` within `a · T n` (from `hL`) and a constructibility
witness within `b · (T n + 1)` (from `hT`; note `TimeConstructible` also
gives `∀ n, n ≤ T n`).

1. **Masked clock**: run the witness with every non-blank input read
   *substituted by `some false`* in its transition table — its entire run
   then coincides with its run on the all-`false` input of length `n`
   (prove this as a lockstep lemma: the substituted machine's configuration
   on input `x` equals its configuration on `List.replicate n false` at
   every step — positions, tapes, state, output), so its trajectories and
   halting time depend only on `n`, and it still emits `⌞T n⌟` (its spec
   holds on the all-false input in particular). Store the budget.
   The witness is *not oblivious in general* — but its masked run is
   length-determined, which is all `Oblivious` needs.
2. **Input copy and park**: one fixed scan copies `x` to a work tape
   (positions during the scan depend only on `n`), then the real input head
   parks for good (every subsequent action moves it by `.zero`) — after
   parking, the input-position component of `Oblivious` is trivially
   length-determined.
3. **Fixed layout**: `B n = (a + 1) · (T n + 1)` macrosteps over a marked
   zone of size `O(B n)` holding the decider's work tapes (fixed-width
   binary blocks), the virtual input copy, virtual head markers, and a step
   counter.
4. **Fixed sweeps**: each macrostep is a fixed number of full sweeps of the
   layout — the sweep path and duration are functions of `n` and the
   macrostep index only; the simulated step happens *en passant* (markers
   and contents change; the trajectory does not). After the simulated
   decider halts, sweeps idle identically. Exactly `B n` macrosteps.
   The `Sweep.lean` transductions (`sweep_run`, `sweep_run_reverse`,
   `sweep_generate` — all with *exact* costs, which is what a trajectory
   argument needs) and `source_bounds` (the decider's heads stay in
   `[-t, t]`, justifying the layout size) are your friends.
5. **Fixed finish**: emit the stored answer bit at a fixed final time, halt.

Cost: `O(b (T n + 1) + n + (B n)²) = O((T n + 1)²)` using `n ≤ T n`;
existential `c` absorbs everything.

**Obliviousness proof shape**: define the schedule (position functions of
`n` and `t`) explicitly or implicitly, and prove by induction on `t` that on
any two same-length inputs the configurations agree on *positions* (input
and all work heads) while possibly differing in contents/state — a
"trajectory lockstep" binary invariant over pairs of runs. Design your
transition table so that every branch on data moves heads identically (the
standard trick: branch only on marker/schedule information for movement;
data selects what to *write*).

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`, branch
  `complexity/arora-barak-ch1`. **Base commit: `71721842`**; branch
  `fill/epoch3-C`; no push/PR.
- **Zip contents** (standard): `REPORT.md`; the modified source file at its
  repository path; `epoch3-C.patch` (`git format-patch 71721842 --stdout`);
  `epoch3-C.bundle`; `final-sweep.log`; `axioms.log`
  (`#print axioms Complexity.oblivious_of_mem_DTIME`, expected
  `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`** — the
  hypotheses supply the decider and witness; no sorry'd theorem is needed);
  `SHA256SUMS`.
- Read first: `policy.md`, plan §5, the target's docstring sketch
  (binding), `audits/phase2-findings.md` finding 2 and
  `audits/phase2-reaudit-findings.md` (the corrected design's audit trail),
  `audits/epoch2-resolutions.md` (the finding-9 obligations above).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean`

The `Oblivious` definition is **frozen**. Private helpers above the target.
If the file passes ~1000 lines, record an escalation in `REPORT.md`
(precedent exists) rather than splitting shared structure. Generic new
gadgets → `private` copy + "Requested shared lemmas".

## Environment and verification

- `lake exe cache get` once; **never `lake build`**; verify per module with
  `scripts/lean_check_tree.sh` (strengthened gate), full 25-module sweep
  before delivery:
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
- Note `Oblivious.lean` sits mid-order; re-check it and everything after it.
  Pass = exit 0, zero `error:` lines, sorry warnings only at:
  `exists_effectiveMachineCode` (Encoding.lean), `universal`,
  `timed_universal` (Universal.lean) — your tree at your base.

## Ground rules (binding)

1. **File ownership**: only `Oblivious.lean`; every new declaration listed
   in `REPORT.md`. 2. **Statement freeze** (the rendering of `Oblivious` and
   the `TimeConstructible` hypothesis were audit-settled; unprovable-as-
   stated = escalation with analysis, never an edit). 3. No other sorry
   touched. 4. Sketches stay (append implementation notes, flagged).
   5. Precise imports; keep `set_option` headers.

## REPORT.md checklist

- [ ] Target filled; the masked-clock lockstep lemma named; how the schedule
      is defined and how the trajectory-lockstep invariant is stated; where
      idling is implemented; the cost ledger.
- [ ] Confirmation that `Oblivious` was verified on *all* inputs of each
      length (including lengths where `DecidesInTime`'s outputs differ, and
      empty input).
- [ ] New private declarations listed; requested shared lemmas — or "none";
      escalations — or "none"; docstring appendices — or "none".
- [ ] Verification evidence: final sweep log, axiom log, zero `error:`
      lines, exact remaining sorries.
- [ ] Diff touches only `Oblivious.lean`.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne`; core `Nat.pow_pos`; no `dite_eq_right/left` —
  `split <;> simp <;> omega`; `dsimp only` after `cases hs : cfg.state`;
  targeted `simp only` (never bare `simp` against folded hypotheses;
  `initCfg` is `@[simp]`); `ring` needs `import Mathlib.Tactic.Ring`;
  normalize `Fin.val ⟨e,h⟩`/un-beta'd lambdas before `omega`; SignType names
  `SignType.coe_one`, `neg_eq_neg_one`, `coe_neg_one`, `pos_eq_one`,
  `zero_eq_zero`; work tapes are ℤ-indexed `Option Bool` via
  `Function.update`; `Cfg.ext` for configuration equality; the run algebra:
  `MultiTapeTM.step_of_halt`, `runFrom_of_halt`, `runFrom_add`,
  `runFrom_succ_eq_step'`, `runFrom_comm_of_step`.
- `DecidesInTime` unfolds to `ComputesInTime x [indicator …] (T x.length)`;
  `Turing.FinTM.computesInTime_iff` drops the space witness;
  `output_unique`/`mono` as usual. `TimeConstructible` gives the witness
  machine via its second conjunct — destructure it early.
- Worked exemplars: `sweepTM`'s macrostep discipline (SingleTape.lean —
  *not* oblivious, but the sweep bookkeeping transfers), the `Sweep.lean`
  exact-cost transductions, `counterTM` (budget on a tape), `palTM`
  (copy-then-park pattern at small scale), and for two-run lockstep
  invariants the `StateRenaming`/`bufferedSecondCfg` commutation style —
  yours relates two runs of the *same* machine on different inputs instead.
