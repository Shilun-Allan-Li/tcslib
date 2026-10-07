# Fill campaign — Epoch 4, Batch A: the time-bounded universal machine

## Context

This is the **final fill of the campaign**: `Turing.timed_universal` is the last
of the 21 audited sorries. Everything else is proved — in particular the untimed
evaluator `Turing.universal` is fully machine-checked, and its entire
construction is now **public infrastructure** across three modules
(`UniversalStartup.lean`, `UniversalInterpreter.lean`, `UniversalBlock.lean`,
split out at the epoch-3→4 merge). Your job is to extend that interpreter with a
deadline clock and an output buffer, and close the one remaining sorry in
`TCSlib/Complexity/TuringMachine/Universal.lean` (now a 208-line file holding
only the three public statements).

The statement and its docstring sketch are **frozen** — read them in
`Universal.lean`. They went through the phase-3 audit (two rounds) and the
epoch-3 audit confirmed implementability atop the delivered infrastructure.

## The statement, unpacked

For every effective scheme `c` there is a single machine `U` such that for every
code `α` there is a constant `C` with, for every input `x` and deadline `t`:

- **Success clause**: if the denoted machine halts on `x` with `output` within
  `t` steps (deadline **inclusive** — first halting exactly on transition `t`
  counts), then `U` on `pairEncode (pairEncode (Nat.bits t) α) x` computes
  `true :: output` within `C · (t + 1)²`.
- **Timeout clause**: if no output witnesses halting within `t`, then `U`
  computes `[false]` within the same budget. At `t = 0` no initialized machine
  has halted (`Turing.FinTM.not_computesInTime_zero`), so budget zero **must**
  take the timeout branch — while still parsing its delimiters.

Note the input layout: the *outer* pair doubles its first component, which is
itself the pair `pairEncode (Nat.bits t) α` — so on the tape the clock bits are
doubled twice, `α`'s bits once, and `x` is verbatim. The clock-and-code prefix
has length `4·|Nat.bits t| + 2·|α| + 6`, independent of `x` (epoch-3 audit).

## Binding obligations (epoch-3 audit, finding 8 — carried verbatim)

The epoch-3 auditor certified the sketch implementable atop the B2
infrastructure and enumerated exactly these obligations. They are binding:

1. **Separate the clock from `α`, and send only `α` to `c.canonizer`.**
   Canonizing the clock-dependent outer payload would decode the wrong machine
   and introduce an uncontrolled canonizer cost.
2. **Buffer emissions** on a work tape instead of emitting them (their total
   length is at most `t`, by `Turing.MultiTapeTM.output_length_le`); the real
   output happens only at the end: the success tag, then the flushed buffer —
   or `[false]`.
3. **Decrement the clock once per simulated source transition.** The countdown
   work is a constant multiple of `(t + 1) · (|Nat.bits t| + 1)`; with
   `|Nat.bits t| ≤ t + 1` this fits the quadratic allowance.
4. **Intercept source halting before native halting**, so the success tag and
   buffer can be emitted after the simulated machine halts (the untimed
   interpreter halts natively with the source; yours must not).
5. Budget zero still contains delimiters and must produce `[false]`; first
   halting on transition `t` is a success (the deadline is inclusive).

## What you have (all proved, all public — read these modules end to end)

- **`UniversalStartup.lean`** (591 lines): the pairing arithmetic
  (`universal_pair_*`), the prefix extractor `universalPrefixTM` with its exact
  start/live lemmas, the canonizer stage `universalCanonTM` (buffered execution
  of `c.canonizer` from an extracted code), and the capture wrapper
  `universalCaptureTM` family with `universal_captured_table` — native
  emissions captured on a work tape, then control transferred to a framed
  inner machine. The capture wrapper is your model for output buffering.
- **`UniversalInterpreter.lean`** (1020 lines): the fixed finite controller
  `UniversalControl`, the four-tape `universalInterpreter` and the assembled
  `universalTM`, the virtual-input boundary (`universalInput_read/_move`), the
  unary state tape and its window lemmas, the administrative gadgets (table
  rewind, count-field scan, initial-state skip, unary copy, marker-directed
  state rewind), the checkpoint relation `universalRelation` with
  `universalRelation_start/_halt/_output`, and the generic assembly
  `universal_block_run` / `universal_from_blocks` (forward `(S+B)·(t+1)` and
  the divergence-covering converse, from explicit hypotheses).
- **`UniversalBlock.lean`** (794 lines): the completed live block —
  record-shape and skipping lemmas, `universal_select`, `universal_read_fixed`,
  `universal_prepare_next`, `universal_apply_record`, run concatenation
  `universal_run_join`, and `universal_live_block` (one complete table
  lookup/application within `universalBlockBound = 3L + 5N + 20`).
- The proof of `Turing.universal` in `Universal.lean` shows how these assemble;
  `Turing.universal_quadratic`'s proof shows the constant-composition pattern
  for quadratic budgets.

Suggested shape (not binding): a new outer machine that parses the doubled
outer pair (recovering `Nat.bits t` onto a clock tape and leaving
`pairEncode α x`-shaped work for the existing stages), runs the canonizer on
`α` only, then interprets with three additions per simulated step — decrement,
buffer instead of emit, and a post-halt output phase. A `universalRelation`-style
checkpoint relation decorated with the remaining budget, fed to
`universal_from_blocks` or to a bespoke induction via `universal_run_join`,
both work; choose whichever fits.

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`, branch
  `complexity/arora-barak-ch1`. **Base commit: `ff2161e4`** (the epoch-3→4
  merge refactor). Work branch `fill/epoch4-A`; no push/PR.
- **Zip contents** (standard): `REPORT.md`; the modified source file(s) at
  repository paths; `epoch4-A.patch` (`git format-patch ff2161e4 --stdout`);
  `epoch4-A.bundle`; `final-sweep.log` (the full 34-module sweep — expected
  to show **zero** `declaration uses 'sorry'` warnings: this fill completes
  the campaign); `axioms.log` (`#print axioms Turing.timed_universal`,
  expected `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`** — plus
  regression prints for `Turing.universal`, `Turing.universal_quadratic`, and
  `Complexity.HALT_not_computable`, which must all stay clean); `SHA256SUMS`.
- Read first: `policy.md`, plan §5, `Universal.lean` (the frozen statement and
  sketch), the three infrastructure modules, `audits/epoch3-findings.md`
  (finding 8 and the timed-theorem analysis), `audits/epoch3-resolutions.md`.

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Universal.lean` — close the
  `timed_universal` sorry. New private helpers live here, above the theorem.

You may **not** modify `UniversalStartup/Interpreter/Block` (audited public
surface) or any other file. If an infrastructure lemma is missing a slight
generalization you need, keep a `private` copy in `Universal.lean` and record
it under "Requested shared lemmas" in `REPORT.md`. If the file passes ~1000
lines, record the escalation (precedent exists); do not split it yourself.

## Environment and verification

- `lake exe cache get` once; **never `lake build`**; verify per module with
  `scripts/lean_check_tree.sh`, full **34-module** sweep before delivery:
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
- Pass = exit 0, zero `error:` lines, **zero** sorry warnings anywhere.
- Batch-B environment note: if `lake exe cache get`'s leantar installer hits an
  archive-ownership error, recovery that worked: the compiled cache executable,
  a writable cache directory, `TAR_OPTIONS=--no-same-owner`. Record deviations.

## Ground rules (binding)

1. **File ownership**: only `Universal.lean`; every new declaration listed in
   `REPORT.md`. 2. **Statement freeze** on all public declarations — if you
   believe `timed_universal` unprovable as stated, that is a first-class
   **escalation** with your obstruction analysis, never an edit. 3. No
   infrastructure module touched. 4. The docstring sketch stays (append an
   implementation note, flagged, if your construction deviates). 5. Precise
   imports; keep `set_option` headers.

## REPORT.md checklist

- [ ] Target filled; `sorryAx` gone from `timed_universal`; the three
      regression prints unchanged and clean.
- [ ] How each of the five binding obligations is discharged (name the
      lemma(s) per obligation).
- [ ] The realized cost ledger: startup (outer parse + canonizer), per-step
      (block + decrement + buffering), output phase; how `C` is assembled and
      why it is `α`-only.
- [ ] The deadline-inclusive boundary argued explicitly (halting detected
      after transition `t`), and the `t = 0` timeout case.
- [ ] New private declarations listed; requested shared lemmas — or "none";
      escalations — or "none".
- [ ] Verification evidence: full 34-module sweep log with **zero sorries**,
      axiom log, zero `error:` lines.
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
- **Per-module `match` auxiliaries**: Lean mints `match`-compiler constants
  per module. Rewriting against another module's `match`-defined declaration
  works through that module's *public lemmas*, but restating the same `match`
  syntactically in your file mints a *different* auxiliary and `rw`/`simp
  only` will not bridge them (this constraint shaped the epoch-3→4 split
  boundaries). Prefer the exported equation lemmas of the infrastructure over
  re-deriving definitional shapes.
- Closest exemplars, ascending relevance: `bufferedCompTM` and its `_run`
  lemmas (`Simulation.lean` — virtual input service), `universalCaptureTM`
  (`UniversalStartup.lean` — emission capture + control transfer: the model
  for your buffer), `universal_live_block` + `universal_run_join`
  (`UniversalBlock.lean` — per-step block concatenation), and the proof
  bodies of `universal` and `universal_quadratic` (`Universal.lean` —
  assembly and constant composition).
