# The campaign records

Process records of the quantum computation and complexity campaign: the plan, audit gates,
fill rounds, design notes and logs. The library itself is `TCSlib/`; the standards are
`policy.md` and `workflow.md` at the repository root.

These records live on the branch `quantum/campaign` and are kept off `main`, following the
Arora–Barak chapters 3–4 campaign (`complexity/arora-barak-ch3-4`). Only Lean code, with the
blueprint and reference files that go with it, is merged to `main`.

## Layout

The layout is the one used by the Arora–Barak campaign. A folder is created when its first
record arrives.

| Folder | Contents |
|---|---|
| `design/plans/` | the campaign plan, `QuantumComplexityPlan.md` |
| `design/` | design proposals |
| `standards/` | the audit template and any fill-environment addendum |
| `gates/<NN>-<slug>/` | one folder per audit gate: `pack.md`, `findings.md` (verbatim), `resolutions.md`, later rounds as `pack-r2.md`, `findings-r2.md`, plus `evidence/` and `logs/` |
| `fills/<group>/` | one folder per fill workstream: `briefs/`, `reports/`, `reviews/`, `logs/`, `evidence/`, `integration/` |
| `items/<workstream>/` | workstream-level design notes and evidence |
| `logs/` | logs not tied to one gate or fill |
| `backlog.md` | the running backlog and open-question register (opened with the first gate) |

## Gates

| Folder | Files | Status |
|---|---|---|
| `gates/01-quantum-phase1/` | `pack.md`, `findings.md`, `pack-r2.md`, `findings-r2.md`, `resolutions.md`, `kickoff.md`, `kickoff-r2.md`, `evidence/`, `evidence-r2/`, `evidence-close/` | **closed** 2026-11-09, round 2 (closing commit `13c8664b`) |
| `gates/02-quantum-e1/` | `pack.md`, `kickoff.md`, `evidence/` (diff, bundle script); fill evidence in `fills/e1/evidence/` | **open**: round 1 pending |
