# Gate 34 · resolutions, round 2 · CLOSED

Codex: **CLEAR**, 0/0/0/0.
- **Findings:** `findings-r2/gate34-sc-ot-r2-findings.md`, SHA-256 `ea3e0b0a2a1368a71638bb83756050aa3acee58354de4137d932c622acd7b778`.
- **Audited:** head `b0bad23ae611983e3323460bb8c564da90ad6e8c`, records `4c95a843`, exchange `7add7297`.

| # | Round 1 | Round 2 |
|---|---|---|
| G34-01 | major | **Closed.** Fixed by LE-gate34: both readers now come from `headD_drop`, and only the proofs change. |
| G34-02 | major | **Closed as accepted ledger debt (DL-48).** The cleanup promotes `length_ofFn_coins` to the `NUPPT` layer and re-points both copies. |

What else Codex confirmed:
- The rebase's range-diff is 5/5 identical, and the base delta is #316–#317.
- All 193 headers are unchanged, and the statement counts are still 141/0/0.
- The 270-module integration build checks out, as do the Rule-10 probes and controls.
- The axioms are standard, admissions go 216 → 214, and lint is unchanged.
- No new duplication was found.

**Gate 34 is CLOSED.** One merge condition remains: the combined build of all open PRs on the tip that includes #313. That build is running.
