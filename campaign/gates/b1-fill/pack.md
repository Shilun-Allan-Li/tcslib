# External audit pack — epoch 2, B1 light half: the oracle-machine layer (P0) and eight filled targets

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e). B1
is the oracle-machine cluster. Its statements were audited at phases P3.1
and P3.2: `audits/ch3-p31-*` and `audits/ch3-p32-*`, attached, whose
per-statement arguments are the binding routes.

This round audits **one maintainer PR** (#26, `integrate/b1-oracle`), which
does two things:

- **P0** lands a small oracle-machine library layer.
- **Eight light B1 targets** are filled. The proofs were written in the
  B1 research route check and turned into final files.

`POracle_eq_P_of_mem_P` is **deferred, untouched**, to a shared oracle-call
simulation extension. The integration record is `audits/b1-integration.md`.
Fill gates close on zero blockers and zero majors (`workflow.md` §4). The
duplication rule (`audits/TEMPLATE.md`, failure mode 5) is in force.

**The audit object.** Every proof is kernel-checked (replay below). What you
audit is the **surface**:

- P0's new public contracts;
- the eight proofs' fidelity to the binding routes;
- the frozen statements;
- duplication.

## What changed (verify)

| File | Change |
|---|---|
| `TuringMachine/Finite.lean` | **New public** `MultiTapeTM.exists_first_halt`. Seven private copies elsewhere (`EXP`, `SAT` ×2, `Hardness`, `Catalog` ×2, `Loop`) are recorded as backlog FH-1, files not edited |
| `TuringMachine/Oracle.lean` | **11 new publics**: `step_of_halt`, `runFrom_succ_eq_step'`, `runFrom_add`, `runFrom_of_halt`, `runFrom_comm_of_step`, `ComputesInTime.mono`/`.output_unique`, `runFrom_eq_of_forall_ne_qQuery`, the bridge `runFrom_eq_plainEmptyOracle`, `queryString_eq_of_cells`, and `queryString_length_le_of_blank` (C1-P1, promoted from C1c's private copy). `queryString_length_le` now cites it, statement byte-identical |
| `TuringMachine/OracleFinite.lean` | bundled `mono`, `output_unique` |
| `TuringMachine/OracleNondeterministic.lean` | the private blank-cell bound is deleted (moved); E5 cites the public one |
| `TuringMachine/Build/OracleCall.lean` (new) | `queryString_bufferTape`, `answerAction`, `step_of_qQuery`, `step_of_answerAction`, `runFrom_two_of_qQuery`, `capture_reaches_qQuery` (query-tape capture: W1 with `ret := qQuery`); wired into the `TuringMachine` facade |
| `ClassOracle/Classes.lean` | targets `mem_POracle_of_polyTimeReducible`, `oracle_mem_POracle`, `compl_mem_POracle`, plus 9 privates. `POracle_eq_P_of_mem_P` is unchanged |
| `ClassOracle/SATOracle.lean` | `compl_SAT_mem_POracle_SAT`, `NP_subset_POracle_SAT`, `coNP_subset_POracle_SAT` |
| `Diagonalization/Relativization.lean` | `unaryWitnessLang_mem_NPOracle` and the stage construction `exists_oracle_ne`, plus 40 privates (412 → 961 lines) |

## Brief for the auditor

1. **Freeze.** From the attached patch and sources, confirm:
   - no existing statement changed and no public was removed;
   - the changed bodies are exactly the 8 targets, `queryString_length_le`
     and E5;
   - `POracle_eq_P_of_mem_P` and every other out-of-scope sorry are
     byte-identical;
   - the only private removed is the moved bound.
2. **P0's public surface.** Blind-restate each of the 20 new public
   declarations. Is each true as stated, minimal, and placed in its natural
   home? Two need particular attention:
   - **`runFrom_eq_plainEmptyOracle`**, the bridge from plain contracts to
     oracle runs. State exactly when it applies: every reached state before
     the horizon differs from `qQuery`. Confirm it is not vacuous, and that
     it cannot let a consumer skip a query.
   - **`capture_reaches_qQuery`**, the query-tape capture. Check the final
     configuration, and that the capture tape *is* the query tape, with no
     seam glue hidden in a hypothesis.

   Also: `exists_first_halt` replaces seven private copies by citation. Is
   its statement the common strength they all need?
3. **The two mirrors.** `Oracle.lean`'s `runFrom_comm_of_step` (100% in both
   directions, 63 characters) and `ComputesInTime.output_unique` (83%)
   mirror their plain-machine counterparts. The maintainer approved them as
   forced, since the machine types differ. Rule under failure mode 5: forced
   and harmless, or a sign that the oracle layer should derive from the
   plain one?
4. **Route fidelity.** Compare each of the eight proofs with its binding
   route in the P3.1/P3.2 findings:
   - the reductions and complements, via query-tape capture and the
     four-state tail;
   - `oracle_mem_POracle`, by a single query;
   - the SAT corollaries;
   - the unary witness;
   - the stage construction over `OracleAgreement` and the enumeration.

   Report any proof that re-derives a cited lemma instead of citing it.
5. **The stage construction.** `exists_oracle_ne` is the batch's largest
   proof: 961 lines in `Relativization`, with 40 privates. Check its
   decided-length choice (max of `nᵢ` and the budget, as the P3.2 audit
   prescribed), the oracle extension, and the diagonal argument against
   every machine of the enumeration.
6. **Duplication (failure mode 5).** The screen goes from 390 to 397 pairs,
   with none gone (`audits/logs/b1-integration-screens/`). The seven new
   pairs:
   - the two mirrors (question 3);
   - three glue pairs at 54–71%: `uw_tail` → E3, `uw_scan_step` →
     `uw_false_step`, and `Catalog.f2_loopBody_step` → `queryTM_init`;
   - one artifact, `runFrom_ofMultiTapeTM` → `runFrom_plainEmptyOracle`
     (53%). Both are unchanged declarations; the new lemma shortened the
     screened body, and the base ratio was 115/237.

   Rule on each.
7. **Docstrings.** Report any docstring made false. Check the status-text
   updates and the new module documentation.
8. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Replay** (`audits/logs/b1-integration-replay*.log`): 207 modules
  downstream of every changed file, in dependency order (order list
  attached), `ComputationalModels` and the root excluded: **0 errors**. The
  47 sorry warnings are exactly the remaining out-of-scope set: base 55
  minus the 8 targets, none added (`…-sorry-sets.log`). Only the final
  state was replayed, not the intermediate commits.
* **Freeze** (`…-freeze.log`).
* **Axioms** (`…-axioms{,-base,-compare}.{lean.txt,log}`):
  - 86 of 94 existing publics print byte-identically;
  - the other 8 are the targets, now `[propext, Classical.choice,
    Quot.sound]`;
  - the 20 new publics are within that triple;
  - no `sorryAx`.
* **Lint** (`…-stylelint.log`): 0 FAIL.
* **Screens** (`…-screens/{command,before,after,delta}.txt`): the screen
  script, the base and after versions of every changed file, and every
  comparison source except `Build/Catalog.lean` are attached. Catalog is
  unchanged and comparison-only; it is identified by its Git blob
  `5f582dd83dc557f3bc6e5f912d01b53c97b10856` at the base.
* **Evidence boundary.** No delivery zip exists; this is maintainer work.
  The replay, axiom and lint results are maintainer attestations from the
  attached logs.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/b1-fill-findings.md`.
