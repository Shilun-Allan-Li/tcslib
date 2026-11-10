# Foundation representation proofs

The phase-0 external statement gate passed with counts 0/0/0/3. Its verbatim findings
and dispositions are under `audits/lwe-sis-phase0-{findings,resolutions}.md`; intake is
recorded in `gates/00-foundations/r1-intake.json`. This fill begins only after that pass.

**Current status:** all 14 proofs are complete at
`893e921bf2afeca293be9da9d495613bb1486796`. The fresh dependency sweep and axiom checks
pass; see `REPORT.md`. Codex is selected for the separate proof review. The ownership
and verification rules below are the retained fill plan, not a new external dispatch.

## Freeze and ownership

Frozen source: `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`.
Own PR branch: `cryptography/lwe-sis-encoding-proofs`.
PR target: `cryptography/pass-shelat-ch2-4`.
The 14 target names/signatures are exactly those in
`gates/00-foundations/evidence/admissions.json`.

Root edits and commits only in the own checkout. Two user-authorized internal agents
perform read-only lemma/proof research, without native/cache jobs, edits or dispatches.
Root runs one native module at a time using the own pinned packages and olean tree.
No external fill worker is dispatched. All Lean changes are for a user-approved PR.

## Targets

* `Encoding/Modular`: vector/matrix lengths and injectivity (4).
* `LWE/Encoding`: challenge length and injectivity (2).
* `LWE/Assumption`: polynomial input bound (1).
* `SIS/Encoding`: matrix length/injectivity, signed output length and two round trips (5).
* `SIS/Assumption`: polynomial input/output bounds (2).

Use existing public numeral, fixed-block list, matrix and polynomial APIs. No machine
host is needed: these are finite representation identities and arithmetic inequalities.
Do not build a private sampler/runner or duplicate an existing proof. Any needed private
mathematical helper must be recorded; any new public API or changed frozen statement
is escalated instead of silently changing the audited surface.

## Verification and limits

Iterate through `scripts/lean_check_tree.sh` one module at a time, recording owned PIDs
and complete logs. At the fill boundary, run a fresh scoped dependency sweep, signature
and declaration drift checks, style checks, and fresh axiom/constant inventory. Do not
run `lake build`, borrow scratch objects, change package pins or use an unfiltered cache.
Use `python3 -I` for Python. Root's native/cache work is serial within the previously
approved resource increase.

The three external notes remain in force. This fill does not prove hardness, efficiency
of honest samplers, correctness/security of a primitive, or source-policy completion.
It does not authorize a merge. The next external review still requires the user's
worker selection and dispatch under the exchange protocol.

**Not yet clear to merge — all 14 proofs pass native checks; external proof review,
source archival and user-controlled integration remain open.**
