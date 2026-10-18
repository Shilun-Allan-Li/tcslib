# B2b fill, first delivery (partial, 0/2 closed): integration record

Brief: `briefs/ch34-b2b.md` (ancestor `2483ff81`). Delivery: `infra_local/fill-ch34-b2b.zip`,
agent commit `5137a0b7` on base `aed5b4ff`, the campaign tip. The agent's report is
`audits/b2b-fill-agent-reports/fill-1-REPORT.md`.

## Result

**Neither target is closed.** This is a partial delivery under the continuation provision
(ground rule 9). There is no escalation, and no counterexample or incompatible row: the agent
stopped at its budget.

| Target | Status |
|---|---|
| `NP_subset_PSPACE` | public packaging proof assembled around **one admitted private helper**, `b2b_host_contract` (`Inclusions.lean:740`, with a literal Proof sketch) |
| `SAT3_mem_PSPACE` | `NP_subset_PSPACE SAT3_mem_NP`; inherits the admission |

**What is done.**
- The machine is fully defined, with every piece assembled from the prescribed public rows
  through `phaseHostTM`:
  - the shared test `b2b_testTM`, one definition used both in the loop body and in the
    continuation;
  - the loop body;
  - the outer host, with exactly one `counterLoopTM`;
  - the four sanctioned glue machines: rewind, verdict reader, stationary anchor and final
    answer.
- 15 private theorems are proved, among them:
  - the hosted-source run, with its fixed bank-radius trajectory;
  - the certificate orbit and its exact equivalence with the witness quantifier;
  - the buffer concatenation;
  - the polynomial ledger bound, with no factor `2^Q`;
  - the normalization to `PSPACE`.
- The proved-modulo set stays empty, as the brief requires.

**What is open.** `b2b_host_contract` packages the setup (S1–S5), the one shared round
contract, the counter-loop instantiation, the composition with the final test and answer, and
the fixed-window space bound. The report's continuation frontier lists them as five steps,
with the fixed windows and common radius `W(n)` stated exactly.

## Verification (maintainer)

- **Integrity.** All 25 `SHA256SUMS` entries are OK. The zip's C file
  (`environment/lean-self-path.c`, an `LD_PRELOAD` shim for the agent's environment) is
  excluded: it was never compiled or run, and neither the patch nor any source references it.
  The zip contains no scripts.
- **Integration.** `git am -3` applied the one-patch series cleanly at `aed5b4ff` as
  `f10b8c91`, keeping the agent's authorship. `Inclusions.lean` matches the delivered snapshot
  byte for byte.
- **Freeze** (`audits/logs/b2b-fill-1-freeze.log`, the maintainer's own check).
  - No statement changed. No public was added or removed.
  - Bodies changed only at the two targets; `DTIME_subset_SPACE` and `P_subset_PSPACE` are
    byte-identical.
  - 43 named privates added, plus 6 private instances.
  - Exactly the brief's five sanctioned imports were added, under the flagged comment:
    `Build.CounterLoop`, `Build.VirtualInput`, `Build.Seam`, `Machines.Clean`,
    `CircuitComplexity.MeyerTableau`.
  - The only `sorry` among the added lines is `b2b_host_contract`'s. There is no `admit`,
    `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe`.
  - The module status text is unchanged, as is right for a partial delivery.
- **Duplication.**
  - Screens: after, `audits/logs/b2b-fill-1-screen-after.txt`; before,
    `audits/logs/b2b-fill-1-screen-before.txt`.
  - 784 → 817 declarations and 626 → 627 pairs. The one new pair is in-file:
    `b2b_callEmb` ← `b2b_bankEmb` (66%), two explicit `Fin` selections sharing
    `Fin.ext`/`omega` boilerplate, justified in the report.
  - There is no cross-file pair with an `Inclusions` declaration on either side, and no pair
    disappeared. **New copies: none.** No ledger change.
  - **Erratum (screen base).** The issued base file `audits/logs/b2b-screen-base.txt` holds a
    run over a narrower population (665 declarations, 458 pairs). The brief's prose (784 / 626)
    and its command are correct. The agent and the maintainer both reproduce 784 / 626 with
    that command, so `b2b-fill-1-screen-before.txt` is the base of record. The issued file is
    kept unchanged, and the continuation brief cites the corrected base.
- **Lint** (`audits/logs/b2b-fill-1-stylelint.log`): 0 FAIL, 0 WARN over
  `TCSlib/Complexity/SpaceComplexity`.
- **Size.** `Inclusions.lean` grows from 115 to 815 lines.
- **Replay** (`audits/logs/b2b-fill-1-replay.log`). 4 modules, the downstream closure of
  `Inclusions`, at `f10b8c91` into a snapshot of a tip-consistent olean tree; the user ran it
  from the maintainer's command. **0 errors.** 5 sorry warnings: `Inclusions` 1
  (`b2b_host_contract`), `TQBF` 4, both facades 0.
- **Axioms** (`audits/logs/b2b-fill-1-axioms.log`; probe
  `audits/evidence/b2b/B2bFill1Axioms.lean.txt`). Read-only against the replay's tree.
  - `DTIME_subset_SPACE` and `P_subset_PSPACE` keep the standard triple.
  - Both targets print `sorryAx`, as the report discloses.
- **Admission walk** (`audits/logs/b2b-fill-1-admissions.log`; probe
  `audits/evidence/b2b/B2bFill1AdmissionWalk.lean.txt`). For both targets, the only constant
  in the closure that mentions `sorryAx` is the private `b2b_host_contract`. So everything
  else the targets use, every cited library row included, is admission-free.

## Disposition

- This partial goes in by PR. The **B2b fill gate** runs once both targets close.
- A continuation brief for `b2b_host_contract` issues at the merged commit.
  - It keeps the helper's statement and the five-step frontier.
  - It cites the corrected screen base.
  - It keeps the proved-modulo set empty.
