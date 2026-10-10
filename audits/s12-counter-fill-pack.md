# External audit pack — §12.7 counter-driven loops, fill gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4b). The
§12.7 statement gate closed in one round: 0 blockers, 0 majors, 1 minor and
5 notes (`audits/s12-counter-findings.md` and
`audits/s12-counter-resolutions.md`, both attached). This round audits the
**fill**. One batch (brief `briefs/s12-counter-fill.md`, report attached
verbatim) proved all ten audited statements in
`TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean`. Fill gates close on
zero blockers and zero majors (`workflow.md` §4). The duplication rule
(`audits/TEMPLATE.md`, failure mode 5, as amended) is in force.

The fill is the attached single-commit patch
`audits/evidence/s12-counter-fill.patch`. It is Codex-authored, integrated by
`git am -3` as `2e99bda1` at recorded base `c9a0b431`. The campaign tip
`5ad155ee` leaves `CounterLoop.lean` byte-identical to that commit. **Every
proof is kernel-checked**; the maintainer's replay evidence is below. The
audit object is therefore the **surface**:

- the 25 new private declarations;
- the fidelity of the proofs to the statement gate's binding routes;
- the three docstring appendices;
- the duplication rule.

## What changed (verify)

| Change | Declarations |
|---|---|
| **Contracts proved** (the ten sanctioned bodies) | `MultiTapeTM.mapWorkSymbols_runFrom`; `decrementTM_run_succ_ofCfg`, `decrementTM_run_underflow_ofCfg`; `counterWord_length`, `counterWord_value`; `counterOverhead_le_of_le`, `counterOverhead_le`; `counterLoopTM_run_done`, `counterLoopTM_run_escape`; `counterLoop_time_le` |
| **New privates** (25; roles in the report) | symbol step `counter_work_step`; complement layer `counter_dec_complement`, `counter_complement_twice`, `counter_buffer_complement`; the **single decrement transport** `counter_decrement_run`; word arithmetic `counter_dec_spec`, `counter_word_succ`, `counter_dec_zero`, `counter_word_decrement`, `counter_potential`, `counter_word_exhausted`; host glue `counter_last_unselected`, `counter_cfg_eq`, `counter_dec_injective`, `counter_redirect_injective`, `counterSpan`, `counter_span_append`, `counterPatch`, `counter_patch_initial`, `counter_patch_twice`, `counter_patch_frame`; the phases `counter_debit`, `counter_body`, `counter_orbit_succ`; the **single round induction** `counter_rounds` |
| **Docstring appendices** (flagged, prefix-preserving) | the module docstring's "Fill appendix (§12.7)"; the proof-sketch appendices of `counterOverhead_le_of_le` and `counterOverhead_le` |
| **Unchanged by rule** | all 13 definitions, the inductive type, both instances, every statement, every other docstring, and the imports |

## Brief for the auditor

1. **One proof per shared argument** (brief ground rule 3).
   - Confirm that `counter_decrement_run` is the **only** decrement run
     argument, and that both decrement contracts are derived from the §12.6
     increment contracts through it.
   - Confirm that **no decrement trace** exists anywhere in the file: no
     private re-trace of the borrow pass under any name. The brief's route 2
     forbade one.
   - Confirm that `counter_rounds` is the **only** round induction, that
     both host theorems are derived from it, and that `counter_debit` (one
     lemma covering success and underflow) and `counter_body` are its only
     phase arguments.
   - The report says `counter_rounds` has an **unrestricted final state**,
     and that this one form covers both returning prefixes and the last
     escaping round. Verify that this is genuinely one statement and not two
     inductions merged by a disjunction.
2. **Route fidelity.** Compare each proof with the binding routes in the
   attached statement-gate findings: "Symbol transport and framed
   decrement", "Amortized bounds", and "Exact time and final
   configurations". In particular, check:
   - **Symbol transport.** It is a one-step commutation, `counter_work_step`,
     iterated by `MultiTapeTM.runFrom_comm_of_step`, and it does not copy
     `StateRenaming.lean`'s `relabelState_step`.
   - **Decrement.** It uses the four facts the route names: the
     `decFixed`/`incFixed` complement identity, double complement, buffer
     commutation with delimiters, and the leading-prefix length identity.
   - **Amortization.** It uses the telescoping ones-potential
     (`counter_potential`), not Legendre or Kummer. At `r = value` the word
     is all `false`, and the underflow sweep closes the whole-run bound.
   - **Decrement phase.** It transports along
     `MultiTapeTM.runFrom_mapState_of_agreeOn` with
     `emb := ⟨counterLoopDecExit a, _⟩`. The good set is the non-`done`
     phases, and the guard is the decrement contract's no-earlier-verdict
     clause.
   - **Body phase.** One explicit first step is followed by guarded
     transport with `emb := ⟨counterLoopRedirect a exit, _⟩`. The good set
     avoids the anchor and the exit, and the guard **excludes the endpoint**,
     where the redirection happens.
   - **Edge cases.** The `d = 0` case holds for every `c.state`. Escape at
     the last allowed round, `r₀ = value − 1`, has no trailing underflow.
     Time and the final configuration are exact, with no dispatch steps.
3. **The transports are sound.** The proofs rest on two injectivity facts,
   `counter_dec_injective` and `counter_redirect_injective` (anchor priority
   when `exit = some a`). Verify both, and verify that each guard is
   discharged at every time strictly before the phase endpoint, not at the
   endpoint itself.
4. **The SC-1 range.** `counterWord` freezes at zero while the machine wraps,
   so `counterOverhead` equals the physical cost only for `r ≤ value + 1`.
   Verify that no proof uses `counterOverhead` or `counterWord` outside that
   range in a way that would make a step unsound. A proof that stays inside
   the range is enough.
5. **Freeze.** Re-establish from the attached patch:
   - all 24 public statements are byte-identical;
   - exactly the ten theorem bodies changed;
   - the 13 definitions, the inductive type and both instances are unchanged
     in full;
   - only `CounterLoop.lean` changed, and its imports did not.

   Two independent checks agree, the agent's and the maintainer's, and both
   are attached.
6. **Duplication (failure mode 5).**
   - The brief's binding screen is the text-level screen over CounterLoop,
     Catalog, Embed, Loop and StateRenaming, before and after. It must show
     **no new pair with a CounterLoop declaration on one side and another
     file's on the other**. The agent's after-output and the maintainer's
     reproduce exactly.
   - **Four new in-file pairs** appear, all below the brief's 90% copy
     cutoff (60–76%). The report justifies each as glue: complement
     simplifications, and the parallel framed-interface assembly of the two
     decrement contracts. Rule on whether any is a copy that should have been
     factored, notably `decrementTM_run_succ_ofCfg` against
     `decrementTM_run_underflow_ofCfg` at 448/750 = 60%.
   - **Supplementary maintainer screen** (not in the brief's list):
     CounterLoop against Primitives, Seam, Wrappers and Simulation.
     Primitives holds RB5's `emitterP2_call_phase`, the "one explicit step,
     then guarded transport" pattern the brief said to follow but not copy.
     The screen finds no CounterLoop pair with Primitives. It finds one pair
     with Seam: `counter_work_step` reproduces `seamComp_step_right` and
     `seamRelease_step_right` at 79/135 = 59%. These are 135-character
     sources. Rule on whether this is idiom or a copy.
7. **Docstrings.** Report any docstring whose *content* the fill made false,
   and check that the three appendices describe the proofs as delivered.
   **One staleness is declared, kept under the docstring freeze:** the module
   docstring's "Status: statement skeleton" paragraph and its "All sorried
   (statement phase)" lead-in to *Main results*. The fill appendix says the
   labels are retained historically. A maintainer doc-only refresh follows
   this gate, as for `Build/{Embed,Seam,Catalog}` (`0dca06f6`). Confirm that
   this is the only stale content.
8. **Size.** `CounterLoop.lean` is 1,205 lines, over the policy's 1,000-line
   mark. The justification is in the plan's decision log: a single-file
   ownership with a frozen surface, split deferred to the 12.2c
   reorganization of `Build/` (tranche T3). Say whether you disagree.
9. Report anything else the fill misstates, in the standard table on the
   standard severity scale.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** `SHA256SUMS` all OK. The zip ships no C or shim
  source, and the patch references none. None of the agent's scripts
  (including its `evidence/verify-freeze.py`) was run by the maintainer.
* **Freeze** (`audits/logs/s12-counter-fill-freeze.log`, the maintainer's
  independent declaration-level check from base `c9a0b431` to `2e99bda1`):
  - 24 public declarations before and after, none added or removed;
  - no statement changed, and exactly the ten sanctioned bodies differ;
  - privates 0 → 25, all additions;
  - the docstring differences are exactly the three prefix-preserving
    appendices.

  This agrees with the report's freeze section.
* **Replay** (`audits/logs/s12-counter-fill-gate-replay.log`, fresh
  `.olean`s at the campaign tip `5ad155ee`): `Build/CounterLoop` and the
  `TuringMachine` facade both exit 0 with **0 errors and 0 sorry warnings**.
  Nothing imports `CounterLoop` yet.
* **Axioms** (`audits/logs/s12-counter-fill-axioms.log`, from the
  maintainer's probe `audits/logs/s12-counter-fill-axioms.lean.txt`): all 24
  public declarations are printed and lie within
  `[propext, Classical.choice, Quot.sound]`. Several are proper subsets, and
  six declarations depend on no axioms. `sorryAx` appears nowhere.
* **Lint** (`audits/logs/s12-counter-fill-stylelint.log`, over
  `TuringMachine/Build`): 0 FAIL. The warnings are the file-size ones.
* **Text-level screen**:
  - `audits/evidence/s12-counter/copytext-before.txt` and
    `copytext-after.txt` are the agent's runs;
  - `copytext-after-maintainer.txt` is the maintainer's reproduction, which
    agrees exactly: 686 pairs and 282,786 characters, against 682 pairs and
    282,115 before;
  - every pre-existing pair is unchanged;
  - the delta is the four in-file pairs above.
* **Supplementary screen** (`audits/evidence/s12-counter/copytext-supplementary.txt`):
  the maintainer's run over CounterLoop, Primitives, Seam, Wrappers and
  Simulation, quoted in question 6.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s12-counter-fill-findings.md`. The gate closes on zero blockers and
zero majors. This completes §12.7 end to end: statements, gate, fill and fill
gate. Its consumers are B5 (the joint uniform interpreter and EXPCOM), the
space hierarchy's clock, and 12.2c item 12 (re-deriving the private clocks).
