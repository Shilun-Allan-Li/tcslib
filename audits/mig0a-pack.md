# External audit pack — MIG-0a: the framed-contract structure (`Build/Contract.lean`), statements and proofs

Campaign: the foundation migration (design §16, backlog MIG-0), under the Arora-Barak chapters
3-4 plan. **MIG-0a** is the first increment of item 0 of the host registry (design §14): one
structure, `Turing.Contract`, that packages what the machine library's framed rows state one
by one, with composition definitions as thin wrappers over the existing public rows. Every later
migration row (MIG-11 to MIG-17) and the RAM-to-`FinTM` compiler's stage 2 will be stated
against it, so its statements must be right before anything is built on it.

**This gate audits the proposed new file and its records together.** The file is written and
proved; it is not landed. Two read-only fit tests by maintainer sub-agents proved every sorried
draft item, changing no statement, and the maintainer re-checked them. The maintainer then added
four items. If the gate closes, the file lands unchanged, together with an import in the
`TuringMachine` facade.

**Bundle:** `audits/mig0a-bundle.md`: this pack, the standards, the design extract (§14, §16, §16a),
the four versions of the file, the logs and the statement-check script, the backlog, and the
core and `Build` files whose rows the structure must fit.

| File | Content |
|---|---|
| `audits/evidence/mig0/Contract-proposed.lean.txt` (888 lines) | **the audit object**: the proposed `TCSlib/Complexity/TuringMachine/Build/Contract.lean` |
| `audits/evidence/mig0/Contract-draft-v1-sorried.lean.txt` | the first statement draft, with the compositions sorried |
| `audits/evidence/mig0/Contract-draft-v2-sorried.lean.txt` | v1's proofs plus the second batch of statements, sorried |
| `audits/evidence/mig0/Contract-draft.lean.txt` | everything proved (the two fit tests), before the maintainer's additions |

## What the file states (verify)

- **`Turing.Contract M entry exits ι x`** (`Γ`, the state type and `ι` in `Type`; user decision).
  Its fields are a precondition, an **exact time**, an **endpoint function** and per-tape head
  intervals `[lo, hi]`, all functions of a data index `i : ι` and the start configuration. Its
  proofs say:
  - the run reaches the endpoint at that time;
  - the endpoint is at an exit;
  - **no exit is reached earlier, the cut including time `0`**;
  - the heads stay in their intervals.
- **Derived:** `within` ("within `B`"), `spaceUsedByTape_le` (through
  `spaceUsedByTape_le_card_Icc`), `Positive`, `mem_Icc_of_abs_le` (radius form ⇒ interval form),
  and `live` (a run is live before its endpoint).
- **Frames, a derived layer** (user decision: not a field): `Cfg.SameOutside` (a per-tape
  footprint), `.trans`, `.mapState`, `.keep_word`, `.keep_blank`, `Contract.Frames` and
  `frames_iff`.
- **Compositions:**
  - `trans`: one machine; times add; needs `hX`;
  - `seq`: the R2 seam; `t₁ + 1 + t₂`; the first phase has a single exit;
  - `inPhase`: the phase host; its exits are the redirect targets, which must lie in another
    phase;
  - `embed`: R1; unselected tapes framed; output appended;
  - `branch`: the two-way seam;
  - `ReturnContract` with `release`: entry = exit, cut from time `1`, through `seamReleaseTM`.
- **Two exports the library lacks**, derived here from public rows and to move to their files'
  rebases: `embedEmitCfg_unselected` (`Build/Embed`) and `seamCompTM_runFrom_right`
  (`Build/Seam`). Also `Cfg.select`, `embedEmitCfg_select` and `Cfg.bindState`.
- **The routine instance:** `clearTM_contract` (R3 clear, from `clearTM_run_ofCfg`) and
  `clearTM_contract_frames`.

## Brief for the auditor

1. **Fidelity to the requirements.** Check the file against design §14 item 0 and §16's list "What
   the contract structure must support" (attached):
   - exact time and the cut as first-class fields, with "within" derived;
   - a positive duration (here `ReturnContract.pos` and `Positive`);
   - an endpoint function and frames (here a derived layer, by user decision);
   - envelopes in radius and interval form, with space derived;
   - the input tape and output appends (the endpoint and `embed`);
   - the transports.

   MIG-0a covers the seam, the phase host, R1, the branch and the release. MIG-0b will cover
   the symbol lift, the counter loop, renaming and the tactics (design §16a). Say whether any
   requirement is unmet or met in a form that will not scale, and whether the MIG-0a/MIG-0b split
   leaves a gap that later rows will hit.
2. **Each statement's strength.** For every composition, are the hypotheses necessary, and is the
   conclusion the strongest natural one? Points to rule on:
   - `seq` requires a single exit of its first phase. Set-valued first phases go through `branch`.
     Is that enough?
   - `inPhase` requires every redirect target to lie in another phase (`q.1 ≠ p`). The fit test
     found this essential for the cut. Is a same-phase redirect needed by any planned host?
   - `branch`'s halting exit is untagged: if both continuations may halt, a halted endpoint does
     not say which ran.
   - `trans`'s `hX`, that the first contract does not pass through an exit of the second.
   - `embed`'s precondition reads the source through `Cfg.select`, which sets the output to `[]`;
     the endpoint appends the host's prior output.
3. **Fit with the library.** A read-only inventory of about 150 contract rows in `Build/` found:
   - 24 exact closed-form times;
   - about 45 cuts that include time `0`, and 4 that do not (the install and emit calls, the
     advancing writer);
   - 25 interval and 12 radius envelopes;
   - single anchors, verdict pairs (`yes`/`no`), loop exits (`done`/`escape`) and halting exits
     (`Zone`);
   - frames written in four idioms, with no frame predicate anywhere.

   Using the attached Build files, check that each kind fits the structure, without proving
   anything. In particular check a radius row (`exists_recordEqTM`), a verdict-pair row, a halting
   row (`exists_zoneShiftInTM`), a returning row (`exists_installCallTM`), and the existential
   (`∃ M …`) rows, which become `∃ … , Contract …`. Say whether the data-index design (`ι`)
   handles rows whose data is read from the input.
4. **Proofs.** Everything is kernel-checked: the elaboration logs show 0 errors and 0 warnings,
   with the standard three axioms. Check that the fit tests changed no statement, by comparing the
   v1 and v2 drafts with the proved file (`audits/logs/mig0a-statement-check.log`). Check the
   maintainer's four additions (`live`, the two exports, `frames_iff`).
5. **Names and placement.** No full-name clash anywhere in `TCSlib`
   (`audits/logs/mig0a-names.log`). The short name `SameOutside` also exists as the memory-level
   `Light.SameOutside` in `TCSlib/Programs`. Say whether that invites confusion. Placing the two
   exports here, rather than in `Embed` and `Seam`, avoids a library-wide rebuild now; say whether
   you disagree.
6. **Documentation and policy** (`policy.md`): the module header and status, every docstring, a
   literal proof sketch on every nontrivial proof, attribution (the [AFM26] design-adaptation
   citation for framing and specification-only calls), and the 100-column limit.
7. Report anything else the file or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Elaboration** (`audits/logs/mig0a-elaboration.log`): the proposed file, elaborated read-only
  against the fills-6 and CH34-D4 replay tree, gives 0 errors and 0 warnings. So did each fit
  test's final file.
* **Axioms** (`audits/logs/mig0a-axioms.log`): every definition and theorem depends on at most
  `[propext, Classical.choice, Quot.sound]`.
* **Statements unchanged by the fit tests** (`audits/logs/mig0a-statement-check.log`): every line
  of each sorried draft appears in order in the next version, except the `sorry` lines.
* **Names** (`audits/logs/mig0a-names.log`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/mig0a-findings.md`. The gate closes when it has zero blockers and zero majors; the file
then lands.
