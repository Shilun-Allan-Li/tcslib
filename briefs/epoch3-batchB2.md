# Fill campaign — Epoch 3, Batch B2: finish `Turing.universal` (continuation)

## Context

This is a **continuation batch**. Epoch-3 batch B delivered an honest WIP: the
universal machine `universalTM c` is fully constructed, its startup, captured-table
correspondence, virtual left boundary, halting correspondence, output equality, and
the entire two-clause forward/converse assembly are **proved**, and exactly **one**
`sorry` remains inside the proof of `Turing.universal` in
`TCSlib/Complexity/TuringMachine/Universal.lean`: the live-source table-lookup and
record-application block. Your task is to close that one obligation. Nothing else.

You start from the WIP branch, keeping its construction. You are free to revise or
replace any `private` declaration on that branch (they are unaudited WIP machinery,
including the definition of `universalBlockBound` if its ledger does not realize),
but the **public statements are frozen** — `universal`, `universal_quadratic`,
`timed_universal`, and everything they cite went through multiple audit rounds and
must remain byte-identical.

## The open obligation, precisely

In `universal`'s proof, after

```lean
  apply universal_from_blocks c (universalTM c) (universalStartupBound c)
    (universalBlockBound c) (universalRelation c)
```

the step-simulation hypothesis is discharged by cases on `src.state`. The halted
case is proved (one-step absorbing halt). The live case has, in scope,
`h : universalRelation c α x src dst` and `hs : ¬src.state = none`, and must prove

```lean
∃ d, 1 ≤ d ∧ d ≤ universalBlockBound c α ∧
  universalRelation c α x ((c.decode α).tm.step src)
    ((universalTM c).tm.runFrom dst d)
```

The B-batch report enumerated the missing pieces; they remain the accurate map:

1. Prove skipping and reading one serialized transition record, including its
   eight fixed action bits and the optional unary successor field.
2. Prove that each consumed state-tape symbol skips exactly nine records, and that
   the finite input/work read offset then selects the action of the source
   transition function in `CodeTM.serialize`'s enumeration order.
3. Prove that decoding/applying that action preserves the checkpoint relation
   `universalRelation`: optional writes, state replacement, native emissions,
   virtual input movement (boundary marker in lockstep, clamped at virtual zero),
   halting next-state fields, and the table-cursor bound.
4. Concatenate those runs (`MultiTapeTM.runFrom_add`) and establish the positive,
   code-only step bound `d ≤ universalBlockBound c α`.

## What is already proved on the branch (do not redo)

All of the following are `private`, proved, and named in `Universal.lean` on your
base branch — read them before writing anything:

- **Startup**: `universalPrefix_start` / `universalPrefix_live` (prefix extraction,
  exact configuration after `2|α| + 2` steps), `universalCanon_start` / `_run` /
  `_complete` (canonizer served from the extracted code via `bufferedCompTM`),
  `universalCapture_*` and `universal_captured_table` (canonizer emissions captured
  on the table tape, off the real output), `universalInterpreter_initialize` and
  `universal_initialized` (full first-checkpoint correspondence: table, unary
  initial state, blank mirrored tape, boundary marker, empty output, suffix head
  parked at the suffix start).
- **Virtual input**: `universalInput_read` (delimiter masking), `universalInput_move`
  (clamped physical movement + marker-head lockstep; suppressed outward left move
  at virtual zero; empty-`x` case covered).
- **Administrative gadgets**: table rewind (`universal_table_rewind`), doubled
  count-field skip (`universal_count_run`), initial-state skip
  (`universal_initial_skip`), unary copy (`universal_unary_copy`), the
  `universalStateWindow*` / `universalStateTape*` erase/append/marker family, and
  marker-directed state rewind (`universal_state_rewind`).
- **Assembly**: `universal_block_run` and `universal_from_blocks` are fully proved
  with explicit hypotheses (forward bound `(S+B)·(t+1)`; converse covering
  divergent source runs with no fairness assumption), and the concrete relation's
  other three hypotheses are discharged by `universalRelation_start`,
  `universalRelation_halt`, `universalRelation_output`.

The controller is `UniversalControl` (fixed finite type: booleans, `Fin 9`,
`Fin 8`, optional `Fin 9`, eight-bit functions — no code-dependent state, no
unbounded counters). The state tape holds `false` at zero and `q` copies of `true`
from one; the boundary tape holds a permanent `true` at integer zero and its head
is the native virtual input position.

## The intended (unproved) cost ledger

The B report proposed, per live block — with `h` the old table cursor, `q` the
source state index, `q'` a live successor index, `P` the serialized length of the
skipped records, `k := 2·|Nat.bits M.numStates| + 2`, `L := M.serialize.length`,
`N := M.numStates + 1`:

| Phase | Intended transitions |
| --- | ---: |
| Read symbols, begin rewind | 1 |
| Rewind table to start | h + 1 |
| Skip doubled count field | k |
| Skip initial-state unary field | q₀ + 1 |
| Consume old state, skip preceding records | q + P + 1 |
| Rewind erased state tape to position one | q + 2 |
| Read the selected action's fixed fields | 8 |
| Halting next-state: detect, apply | 2 |
| Live successor: detect, copy, rewind, apply | 2q' + 5 |

giving `h + k + q₀ + 2q + P + 16` (halting) or `… + 2q' + 19` (live), and with
`h, k, P ≤ L`, `q₀, q, q' < N` the definition `universalBlockBound c α = 3L + 5N + 20`.
**This ledger is a target, not a fact.** If the realized costs differ, adjust the
private `universalBlockBound` definition (it is yours) — the public statement only
needs *some* code-only `C`; do not weaken any public statement to buy slack.

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. **Base: branch
  `fill/epoch3-B` at commit `f191b918`** (parent `71721842` on
  `complexity/arora-barak-ch1`). Work on `fill/epoch3-B`; no push/PR.
- **Zip contents** (standard): `REPORT.md`; the modified source file(s) at
  repository paths; `epoch3-B2.patch` (`git format-patch 71721842 --stdout` —
  the full series, WIP commit included unchanged); `epoch3-B2.bundle`
  (`git bundle create … 71721842..fill/epoch3-B`); `final-sweep.log`;
  `axioms.log` (`#print axioms Turing.universal`, expected
  `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`** — plus the
  regression prints for `Turing.universal_quadratic` and
  `Complexity.UC_computable_of_HALT_computable`, which must both *lose* their
  `sorryAx` in your tree); `SHA256SUMS`.
- Read first: `policy.md`, plan §5, `Universal.lean` end to end (the WIP's
  implementation notes mark exactly what is proved), and the audit trail
  (`audits/phase3-reaudit-findings.md` Arguments B/C/E,
  `audits/epoch2-resolutions.md` finding 9).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Universal.lean` — close the `universal`
  sorry; `timed_universal` stays sorry with its sketch untouched.

The file is already 1668 lines (escalation recorded by batch B; precedent:
epoch-2 SingleTape). Growth to finish the proof is accepted — record the final
size in `REPORT.md`; do not split shared structure yourself. New generic gadgets
stay `private` with a "Requested shared lemmas" entry.

## Environment and verification

- `lake exe cache get` once; **never `lake build`**; verify per module with
  `scripts/lean_check_tree.sh`, full 25-module sweep before delivery:
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
- Pass = exit 0, zero `error:` lines, sorry warnings **only** at:
  `exists_effectiveMachineCode`, `oblivious_of_mem_DTIME`, `timed_universal`
  (your lineage predates the epoch-3 A/C integrations; those two fills are not
  in your tree and are not your concern).
- Environment note from batch B: if `lake exe cache get`'s leantar installer
  hits an archive-ownership error, the recovery that worked is the already
  compiled cache executable with a writable cache directory and
  `TAR_OPTIONS=--no-same-owner`. Record any such deviation in `REPORT.md`.
- Batch B's optional executable interpreter diagnostics crashed with deep
  recursion (exit 134) before returning results; executable smoke tests of the
  whole interpreter are **not required** and evidently not feasible at this
  depth — the module checker and axiom prints are the gate.

## Ground rules (binding)

1. **File ownership**: only `Universal.lean`; every new or changed declaration
   listed in `REPORT.md`. 2. **Statement freeze** on all public declarations;
   if the remaining block is unprovable against the WIP construction, first try
   revising the private construction; a genuine obstruction to the *statement*
   is a first-class **escalation** with analysis, never an edit. 3. No other
   sorry touched. 4. Existing sketches and WIP implementation notes stay
   (append, flagged, when the construction changes). 5. Precise imports; keep
   `set_option` headers.

## REPORT.md checklist

- [ ] The sorry closed; `sorryAx` gone from `universal`,
      `universal_quadratic`, and `UC_computable_of_HALT_computable`.
- [ ] The realized per-block cost ledger (phase table with proved counts) and
      the final `universalBlockBound` definition; whether `3L + 5N + 20`
      survived, and if not, what replaced it and why.
- [ ] Which WIP private declarations were revised or replaced, and which of the
      four enumerated sub-obligations each new lemma discharges.
- [ ] Requested shared lemmas — or "none"; escalations — or "none".
- [ ] Verification evidence: final sweep log, axiom log with the two regression
      prints, zero `error:` lines, exact remaining sorries (must be exactly
      `exists_effectiveMachineCode`, `oblivious_of_mem_DTIME`,
      `timed_universal`).
- [ ] Diff (over the WIP commit) touches only `Universal.lean`.

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
- The closest in-repo exemplars for record scans over a tape are `sweepTM`'s
  use of the `Sweep.lean` transductions and the WIP's own
  `universal_count_run` / `universal_initial_skip` — pattern-match on those
  before inventing a new induction shape.
