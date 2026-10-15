# External audit pack — B2b fill gate: certificate cycling (`NP ⊆ PSPACE`, `3SAT ∈ PSPACE`)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e, cluster B2b). The
statements are [AB09, Example 4.6]'s `Complexity.NP_subset_PSPACE` and
`Complexity.SAT3_mem_PSPACE`, in `TCSlib/Complexity/SpaceComplexity/Inclusions.lean`. Their P4.1
statement gate closed in round 1 with both **true as stated**: `audits/ch4-p41-findings.md`, rows
12–13, notes 8–9, Question 5 and the edge-case table, with resolutions
`audits/ch4-p41-resolutions.md`.

One batch filled them over three deliveries. Each was integrated by `git am -3` with Codex
authorship:

| Delivery | Brief | Integrated | Result |
|---|---|---|---|
| 1 | `briefs/ch34-b2b.md` (ancestor `2483ff81`) | `f10b8c91`, PR #40 | partial: the machine fully defined; 15 theorems; one admitted helper, `b2b_host_contract` |
| 2 | `briefs/ch34-b2b-cont.md` | `cd351471`, `a4354452`, PR #47 | partial: setup S1–S5 and the window-to-cardinality packaging proved; the admission narrowed to `b2b_search_contract` |
| 3 | `briefs/ch34-b2b-cont2.md` | `2041510e`, this PR | **complete**: `b2b_search_contract` proved; both targets admission-free |

After delivery 3 the maintainer made one comment-only commit, `6da48293` (see item 7). The
attached `audits/evidence/b2b/fill-gate/b2b-fill-cumulative.patch` is the whole change to
`Inclusions.lean` from the brief's ancestor to the head.

**Every proof is kernel-checked**; the replay and axiom evidence is below. Fill gates close on
zero blockers and zero majors (`workflow.md` §4), and the duplication rule (`audits/TEMPLATE.md`,
failure mode 5) is in force. The audit object is:
- the frozen surface;
- the fidelity of the construction to the brief's binding route 1;
- the discharge of Question 5's five obligations and the P4.1 notes;
- duplication;
- the documentation.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target bodies, `sorry` → proof** | `NP_subset_PSPACE` (route 1); `SAT3_mem_PSPACE` (`NP_subset_PSPACE SAT3_mem_NP`) |
| **Frozen, statement and body byte-identical** | `DTIME_subset_SPACE`, `P_subset_PSPACE` |
| **Privates, 0 → 64** | the machine: `b2b_host`, `b2b_testTM`, `b2b_bodyTM`, their phase families and redirects, and the four sanctioned glue machines (`b2b_rewindTM`, `b2b_verdictTM`, `b2b_anchorTM`, `b2b_answerTM`); the contracts, from `b2b_hostedSource_run` through the shared trial `b2b_trial_run`, the round `b2b_round_run`, the search `b2b_search_contract` and the host contract `b2b_host_contract`; the pure lemmas (buffer concatenation, counter value, certificate orbit, `b2b_verifies_iff`, the ledger) |
| **Imports** | exactly the brief's five sanctioned ones, under a flagged comment: `Build.CounterLoop`, `Build.VirtualInput`, `Build.Seam`, `Machines.Clean`, `CircuitComplexity.MeyerTableau` |
| **Docstrings** | the flagged "Fill appendix (B2b)" on `NP_subset_PSPACE`; the module's `Main results` tag, now "(proved)"; sketches on every new private |

## Brief for the auditor

1. **Freeze.** Re-establish it from the attached base (`Inclusions.base.lean.txt`, at
   `2483ff81`), the head and the cumulative patch:
   - all four public statements are unchanged;
   - `DTIME_subset_SPACE` and `P_subset_PSPACE` are byte-identical;
   - only the two target bodies changed;
   - the imports are exactly the five sanctioned ones.

   The cumulative patch removes exactly four lines: the status tag, the line ending the
   appendix (re-added extended), and the two `sorry`s.
2. **Route fidelity** (brief route 1, steps A–I, binding).
   - **Assembly.** The machine is assembled only from the prescribed public rows through
     `phaseHostTM`: `counterLoopTM`, `incrementTM`, `vhostEmitTM`, `LogProg.cleanTM_run`, R1/R1′,
     `copyTM`, `clearTM`.
   - **New machines.** The only new machines are the four sanctioned glue pieces, each
     probe-checked (step G).
   - **One-definition rules** (ground rule 7). `b2b_testTM` is one definition, used in the body
     and in the continuation. The round lemma is one lemma. `b2b_rewindTM` is one definition
     with its five instances. The window ledger is one lemma.
   - **Deviations from the letter of route 1.** The continuations restructured the proof, not
     the machine:
     - a shared trial contract, `b2b_trial_run`, used by every counted round and by the final
       call;
     - classical exact round durations, made a function of the configuration by the
       injectivity of the certificate configurations (`ctrVal_enumWord`);
     - the setup proved as one composed run, `b2b_setup_run`.

     Rule on whether these stay inside route 1.
   - **The L row.** Confirm that R8.8 and R8.5e are not used.
3. **Question 5's five obligations** (binding; verbatim in the brief). Delivery 3's report
   names the discharging lemma for each. Check each claim:
   - (1) Exact width, complete enumeration, and "detect overflow" by the count. There are
     `2^Q − 1` counted rounds plus one final call, the setup's single overflow makes `0^Q`, and
     no loop round overflows. Width zero gives one call on `[]`, and empty input does not force
     an empty certificate (the edge-case table).
   - (2) Exactly `x ++ u` is simulated, with the input-head boundary behaviour.
   - (3) The one-bit result is captured internally. The physical output stays `[]` until the
     single final bit.
   - (4) The verifier scratch is cleared and the heads restored before each reuse, with no
     accumulated history.
   - (5) **Fixed windows across every call and reset.** The report's radius is
     `n + Q + cV·((n + Q)^e + 1) + cI + 1`. It comes from the counter loop's public trajectory
     clauses and the rows' framed clauses, and has no factor counting trials. Confirm that no
     step bounds the whole run's space by its (exponential) time.
4. **The P4.1 notes.**
   - Note 8: every space fact rests on space-preserving contracts. A time-only citation would
     discharge nothing.
   - Note 9: `SAT3_mem_PSPACE` is delivered at polynomial strength, and its docstring says so.
5. **The combined tree.** Delivery 3 was built without PR #38's in-place generalization of
   `CounterLoop`, which its search cites. The maintainer checked the tree it lands in: the
   campaign tip with PRs #38 and #43 and both current fill integrations. Check the records:
   - `audits/logs/fills-3-combined-replay.log`, 13 modules, 0 errors;
   - the axiom log run on both trees, with identical output.
6. **Duplication** (failure mode 5).
   - The brief's 14-file population screen: from 784 declarations / 626 pairs before delivery 1
     to 865 / 635 after delivery 3. The other changes between deliveries are stream A's
     Catalog pairs, which landed in between.
   - Exactly two pairs involve `Inclusions`, both in-file: `b2b_callEmb` ← `b2b_bankEmb` (66%)
     and `b2b_trialCfg` ← `b2b_setupCfg` (65%). There is no cross-file pair.
   - On the combined tree the only additions are R8.0b's four accepted `CounterLoop` pairs.
   - The brief's hazards are forbidden: EXP's private enumerator (`enumCont_*` and its
     machines), a second counter or loop host, a re-proved rewind, first-halt or halt-to-live
     argument, and a generic visited-interval lemma. Confirm that none was copied, adapted or
     re-derived.

   All 14 files of the screen population are attached at the head, with the screen script, so
   the final screen can be rerun in full.
7. **Documentation.**
   - Check the fill appendix, the module tag and the private sketches against the proofs as
     delivered.
   - **Maintainer's comment-only change** `6da48293`. The fill kept two private docstrings
     frozen; they described a "continuation frontier … remain open". They now read "Status:
     proved" and name the proving lemmas. The comment-stripped code is identical to the
     delivered file. Ground rule 3 restricts the *agent's* status edits; rule on whether this
     maintainer refresh is acceptable.
8. **Size.** `Inclusions.lean` grows from 115 to 2,880 lines (4 public / 64 private). The
   briefs set no cap and require the helpers to be private in this file, and file size alone is
   not a driver (user, 2026-10-11). Say whether you disagree.
9. Report anything else the fill or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** Every delivery's `SHA256SUMS` was all OK: 25, 50 and 25 entries.
  All three manifests are attached. Deliveries 1 and 2 each carried a C environment shim
  (`lean-self-path.c`, `lean-readlink.c`); neither was compiled or run, and nothing references
  either. Delivery 3 has no C file and no script. No agent script was run. These are maintainer
  attestations.
* **Freeze.** Per delivery: `audits/logs/b2b-fill-{1,2,3}-freeze.log`. Cumulative:
  `audits/evidence/b2b/fill-gate/freeze-cumulative.log`.
* **Replays** (user-run, each with fresh `.oleans` into a tip-consistent snapshot):
  - `audits/logs/b2b-fill-{1,2,3}-replay.log`: 0 errors each. `Inclusions` had 1 sorry warning
    after deliveries 1 and 2 and **0 after delivery 3**.
  - The combined tree: `audits/logs/fills-3-combined-replay.log`, 13 modules, 0 errors.
  - Delivery 3's agent swept 112 modules, then ran its final tail
    (`audits/evidence/b2b/fill-3/agent-final-sweep.log`).
* **Axioms** (`audits/logs/b2b-fill-3-axioms.log`; probe
  `audits/evidence/b2b/B2bFill3Axioms.lean.txt`, read-only).
  - All four publics print within `[propext, Classical.choice, Quot.sound]`.
  - The admission walk from both targets is empty.
  - A census of all 474 private constants of `Inclusions` finds none that uses `sorryAx`.
  - The agent's 15 prints agree (`…/fill-3/agent-axioms.log`).
* **Pre-ship probes.** `audits/evidence/b2b/B2bProbe.lean.txt` with its output, and the
  continuation pre-ship logs: each had 0 errors and no `sorry` of its own.
* **Lint** (`audits/logs/b2b-fill-3-stylelint.log`): 0 FAIL. The warnings are all file-size
  ones.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/b2b-fill-findings.md`. B2b's fill gate closes when it has zero blockers and zero majors.
