# Fill campaign — Epoch 3, Batch B: the universal machine

## Context

You are filling one Lean 4 proof in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1:
`Turing.universal` — [AB09, Theorem 1.9]'s core, the all-string evaluator.
This is the single hardest item of the whole campaign and the last big
summit: every remaining `sorryAx` in the library flows through this one
declaration. Its statement survived a dedicated adversarial audit round
(two blockers were found and repaired *before* it was frozen — read the
module docstring's deviation list; every clause is there for a proven
reason), and the epoch-2 audit re-confirmed the sketch with two binding
design obligations quoted below.

You fill **only `universal`**. `timed_universal` stays sorry (epoch 4
extends your interpreter with a step counter — design for that reuse), and
`exists_effectiveMachineCode` is another agent's batch: your theorem takes
the scheme `c : EffectiveMachineCode` as a *parameter* and must not cite
that existence theorem.

## The statement, unpacked (frozen — read it in `Universal.lean`)

For the given scheme there is **one** machine `U` such that for every code
`α` there is a constant `C` (depending on `α` — this dependence was proved
*necessary*, audit Argument E) with, for every input `x`:

- **Forward**: if `(c.decode α).toFinTM` halts on `x` with `output` within
  `t`, then `U` halts on `pairEncode α x` with `output` within `C * (t + 1)`.
- **Converse**: every completed output of `U` on `pairEncode α x` is a
  completed output of the denoted machine on `x` — so divergence is
  preserved (`U` must *never halt* when the simulated machine diverges;
  intermediate emissions of a non-halting run are unconstrained).

Two binding design obligations from the epoch-2 audit (finding 9):

1. **Prefix-only startup.** `C` may depend on `α` but not on `x`, so startup
   (parsing the code region, canonizing, laying out the table) must read
   only the code prefix of `pairEncode α x` — length `2|α| + 2` — and
   **retain the suffix start untouched**. "The compound input is not just a
   buffered whole word": you cannot copy or scan all of `x` up front, and
   the construction is *not* discharged by `computesFunInTime_comp` plus a
   black box. Add explicit prefix-start and captured-table correspondence
   lemmas.
2. **The virtual left boundary** (phase-4 audit, finding 3, already in the
   sketch): the cell physically left of the verbatim `x` region is the
   pairing delimiter's `true`, not a blank — a simulated machine stepping
   left from `x`'s first cell and branching on blank would be mis-simulated.
   Keep a marker (tape or tracked state/tape combination) for the virtual
   input position; at virtual position zero supply a blank read and suppress
   outward moves, mirroring `Turing.moveInputPos`'s clamp; cover empty `x`.

One more structural constraint the sketch implies but deserves emphasis: the
simulated machine's state space `Fin (numStates + 1)` is **unbounded across
codes**, so the simulated state cannot live in `U`'s finite control — the
sketch's *state tape* (unary, as in `serialize`'s `unaryFin`) is mandatory,
and the per-step table scan matches the unary state region against each
record's self-delimiting fields.

## What you have (all proved, public)

- **The scheme's own canonizer**: `c.canonizer` computes
  `fun α => (decode α).serialize` within `c.canonizerTime` — a *hypothesis
  field*, usable without `exists_effectiveMachineCode`. Startup runs it on
  the undoubled code region. Since the canonizer is a machine expecting its
  argument on the *input tape*, simulate it with its input served from a
  work-tape copy — exactly the **virtual-input technique** of the buffered
  layer (`Simulation.lean`: `bufferTape`, `bufferTape_inputSymbol`,
  `VirtualTag`, `virtualMove`, `virtualMove_correct`, and the
  `bufferedSecondCfg` lemmas as the worked pattern; `bufferedCompTM` itself
  simulates one machine with virtual input already).
- **The sweep layer** (`Sweep.lean`): zippers, exact-cost transductions in
  both directions, `sweep_generate`, `source_bounds` — for the table scans.
- The rewind/emission/branch gadgets (`Simulation.lean`), the composition
  theorems, `computesInTime_iff`, `output_unique`, `output_length_le`,
  `output_prefix`, `Action.apply_workTapes`, `StateRenaming`.
- The serialization grammar: `CodeTM.serialize`'s field dictionaries in
  `Encoding.lean`'s `Serialize` section, and `pairEncode`'s aligned-pair
  structure with `pairDecode`/`pairEncode_injective`.

## Suggested architecture (the audited sketch, in construction order)

1. **Startup (cost a function of `|α|` only).** Scan the doubled region,
   undoubling `α` onto a *code tape*; stop at the aligned `[false, true]`
   separator with the physical input head parked at the start of the
   verbatim `x` region (position `2|α| + 3` in the physical input). Run the
   canonizer virtually from the code tape, capturing its emissions on a
   *table tape*: afterwards the table tape holds
   `(c.decode α).serialize` — the state count, the unary initial state
   (copy it to a *state tape*), and the `9 · (numStates + 1)` records. Prove
   a prefix-start lemma: after exactly this startup, the configuration is a
   canonical "simulation-start" shape whose only dependence on `x` is the
   parked head position and untouched suffix.
2. **Per simulated step (cost a function of `|α|` only — this is `C`).**
   Read the virtual input symbol (physical head walks `x` on demand, with
   the virtual-left-boundary marker of obligation 2) and the simulated work
   symbol (a *work tape* mirrors the coded machine's single work tape).
   Scan the table for the record matching (unary state, input read, work
   read) — the `Sweep.lean` transductions fit; the match is
   finite-state against the fixed field dictionaries plus unary comparison
   against the state tape. Apply the record: update the state tape, write
   and move on the mirrored work tape, move the virtual input head, emit the
   record's output field to the real output. Halting record (`optStateBits`
   `= [false]`) ⇒ `U` halts.
3. **Correctness.** Forward: a run invariant tying `U`'s configuration after
   startup + `s` simulated steps to the coded machine's configuration at
   `s`, with per-step physical cost ≤ some `R(α)`; then
   `C := startup + R` absorbed as `C * (t + 1)`. Converse: `U` emits only
   what the simulation emits and halts only on the halting record, so any
   completed output of `U` is a completed output of the simulated machine —
   this is where administrative liveness matters (startup and scan states
   never halt).

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`, branch
  `complexity/arora-barak-ch1`. **Base commit: `71721842`**; branch
  `fill/epoch3-B`; no push/PR.
- **Zip contents** (standard): `REPORT.md`; the modified source file(s) at
  repository paths; `epoch3-B.patch` (`git format-patch 71721842 --stdout`);
  `epoch3-B.bundle`; `final-sweep.log`; `axioms.log`
  (`#print axioms Turing.universal`, expected
  `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`** — plus
  regression prints for `Turing.universal_quadratic` and
  `Complexity.UC_computable_of_HALT_computable`, which should *lose* their
  `sorryAx` in your tree once `universal` is proved); `SHA256SUMS`.
- Read first: `policy.md`, plan §5, `Universal.lean`'s module docstring and
  sketch (binding), `audits/phase3-reaudit-findings.md` (Arguments B, C, E —
  why the layout, the converse, and the constant are what they are),
  `audits/epoch2-resolutions.md` (the finding-9 obligations),
  `audits/phase4-resolutions.md` (the boundary-marker minor).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Universal.lean` — **only the `universal`
  proof**; `timed_universal` stays sorry with its sketch.

Private helpers above the target. This construction may legitimately be
large; if the file passes ~1000 lines, record the escalation in `REPORT.md`
(precedent: the accepted epoch-2 SingleTape escalation) — do not split
shared structure yourself. Genuinely generic new gadgets (e.g. a reusable
virtual-input-from-work-tape simulator distinct from `bufferedCompTM`'s)
belong as "Requested shared lemmas" entries, kept `private` here.

## Environment and verification

- `lake exe cache get` once; **never `lake build`**; verify per module with
  `scripts/lean_check_tree.sh` (strengthened gate), full 25-module sweep
  before delivery:
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
- Pass = exit 0, zero `error:` lines, sorry warnings only at:
  `oblivious_of_mem_DTIME`, `exists_effectiveMachineCode`,
  `timed_universal` (your tree at your base).

## Ground rules (binding)

1. **File ownership**: only `Universal.lean`; every new declaration listed
   in `REPORT.md`. 2. **Statement freeze** — this statement in particular
   went through two audit rounds; if you believe it unprovable as stated,
   that is a first-class **escalation** with your obstruction analysis, not
   an edit. 3. No other sorry touched. 4. Sketches stay (append
   implementation notes, flagged). 5. Precise imports; keep `set_option`
   headers.

## REPORT.md checklist

- [ ] Target filled; the prefix-start and captured-table correspondence
      lemmas named; how the virtual left boundary is realized; the per-step
      cost ledger and how `C` is assembled.
- [ ] Confirmation that the converse direction's argument covers: divergent
      simulated runs (U stays live), and completed outputs equal simulated
      outputs.
- [ ] New private declarations listed; requested shared lemmas — or "none";
      escalations — or "none"; docstring appendices — or "none".
- [ ] Verification evidence: final sweep log, axiom log (including the two
      regression prints), zero `error:` lines, exact remaining sorries.
- [ ] Diff touches only `Universal.lean`.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne`; core `Nat.pow_pos`; no `dite_eq_right/left` —
  `split <;> simp <;> omega`; `dsimp only` after `cases hs : cfg.state`;
  targeted `simp only` (never bare `simp` against folded hypotheses;
  `initCfg` is `@[simp]`); `ring` needs `import Mathlib.Tactic.Ring`;
  normalize `Fin.val ⟨e,h⟩`/un-beta'd lambdas before `omega`; `Nat.find`
  under classical needs `classical` + explicit `(p := …)`; SignType names
  `SignType.coe_one`, `neg_eq_neg_one`, `coe_neg_one`, `pos_eq_one`,
  `zero_eq_zero`; work tapes are ℤ-indexed `Option Bool` via
  `Function.update`; `Cfg.ext`/`Cfg.ext_zero_tapes` for configuration
  equality; `MultiTapeTM.step_of_halt`, `runFrom_of_halt`, `runFrom_add`,
  `runFrom_succ_eq_step'`, `runFrom_comm_of_step` are the run-algebra
  workhorses.
- Worked exemplars, ascending relevance: `condTM` (phase control + register),
  `bufferedCompTM` + its `_run` lemmas (virtual input serving — the closest
  relative of both your canonizer stage and your simulated-input stage),
  `sweepTM`'s use of the `Sweep.lean` transductions (table scans),
  `counterTM` (unary/binary counters on tapes).
