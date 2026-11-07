# Proposed reading APIs: pending user rulings

2026-11-07. Four separate new-public-API scopes were asked in chat under START-HERE §2.
**All are pending; no library API or fill-scope change is authorized by these records.**
Existing definitions/statements/imports remain fixed and no new global simp attribute is
proposed. The total proposed surface is 19 theorems; the tests below are bounded proposals.

| Scope | Proposed home and surface | Actual evidence |
| --- | --- | --- |
| F6 coded-machine conversion | Encoding: one `CodeTM.toFinTM_eq`, equating the bundle to `{ k := 1, State := Fin (M.numStates + 1), tm := M.tm }` | Same-home syntax and conditional sealed computation/space conversion pass; `campaign/fills/f6/drafts/` |
| MIG-1 left/right configurations | Simulation: five fields each for `FinTM.leftCfg` and `rightCfg`, 10 generated equations | Exact public non-simp generation and conditional sealed reconstruction pass; `config-reader-proposal/REVIEW.md` |
| MIG-1 captured configuration | Wrappers: five `Turing.captureCfg_*` fields | Exact public non-simp generation and conditional output/head/reconstruction checks pass; same review |
| MIG-1 branching | Simulation: `FinTM.branchTM_k`, `_State`, `_runFrom_independent`, 3 theorems | Explicit carrier transport and generic sealed consumer pass; `branch-reader-proposal/README.md` |

For the configuration families, the fields are state, inputPos, workTapes, workTapePos and
output. Work-tape equations are pointwise in tape and cell; head equations pointwise in tape.
The proposed attribute is `simps (config := { isSimp := false })` with those five explicit
projections in the definitions' own homes. Exact formulas/names and failed diagnostic
attempts are preserved in the proposal folders. The capture host's physical output is out₀;
its captured word/head instead use pre ++ c.output.

For branching, the Boolean chooses the initial state. The proposed run contract compares
runs **from the same arbitrary configuration**, after transporting each bundled machine to
the common tape/state types. It is not equality of differently initialized runs. Use the
refined let-view statement in TransportedConsumer-v1.lean.txt, not the earlier raw statement.
The real condTM/timedCondTM host premise and all final consumers remain untested; these
bounded probes do not close the checkpoint's branchTM exclusion.

After the user rules, implement only approved scopes by Lean PR, ask the audit-agent choice
before preparing its gate, and complete the current merged-tree replay. Consumer repairs
must replace implicit rfl/type conversions as well as explicit unfolding arguments and then
pass complete section seals/controls. No proof consumer or API is cleared by this proposal.

Further MIG-24 first-entry sharing is a separately reported gap, not one of these approved
or proposed scopes. T3 same-home factoring, complete seal coverage and final validation
remain required. The immutable MIG-1 brief/base and in-flight Claude job are unchanged.
