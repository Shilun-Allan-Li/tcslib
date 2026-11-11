# Gate 16 · resolutions, round 1

**Status: CLOSED** (0 blockers, 0 majors, 1 minor, fixed). Auditor Codex, 2026-11-11; findings
uploaded by Seyoon and filed verbatim in [findings/](findings/gate16-implications-pk-findings.md)
(SHA-256 `965178cd306b421e36b35378f0feff7658f398c648d82fbfb76ab12c915e6467`).

| Input | Pin |
|---|---|
| Exchange pack | `dcd94a048a40d717083d381ea11f4179acb0d744` |
| PR #292 audited head | `33a616bcc14450b9e3110e4f8801abea1198b2fb` |
| Records | `6c766470019c318eb00dd1ce937406bedef2e9c3` |
| Base | `33cb7ae74c8e6ac23ed5bb1875121eadfe0c2046` |

The auditor verified the pack, bundle, sources and PDF; confirmed the complete premise sets, that
`FixedLengthPKScheme` carries the advertised guarantees, that `msgLen = .var` excludes vacuous
witnesses, and that `AdaptiveINDSecure .cpa` is the adaptive endpoint; checked the composition
step by step (including that the parameter shift keeps the security parameter `n` and the exact
width identities); and inspected the axiom and seal evidence. It did not recompile.

| # | Severity | Resolution |
|---|---|---|
| G16-01 | minor | **Fixed.** The module docstring now calls `AdaptiveINDSecure .cpa` the adaptive multi-challenge extension of [PS10, Definition 171.5] and points to `INDSecure.adaptive_cpa` for the lift (commit `9f5095ad`, docstring only). Rebuild of `Implications/PublicKey`, the facade and `TCSlib` at the new head: rc 0, 0 errors, 0 warnings, each row bound to the head's source hash (`evidence-r2/build.jsonl`). |

**Clear to merge** — #292 at `9f5095adad4c5fd5a5d82f39d71cd678552a26df`.
