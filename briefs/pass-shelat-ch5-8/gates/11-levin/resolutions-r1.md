# Gate 11 · resolutions, round 1

**Status: CLOSED** (0 blockers, 0 majors, 0 minors, 1 note). Auditor Codex, 2026-11-11; findings
uploaded by Seyoon and filed verbatim in [findings/](findings/gate11-levin-findings.md)
(SHA-256 `7d468e6e72d7a9705e5f5fae14d7a8579742bd017fa16246201448bb7952af04`).

| Input | Pin |
|---|---|
| Exchange pack | `117c5882ef91b87cc2489992cea90cdca5661833` |
| PR #286 Lean head | `a1293a6970b4039a9cf19fd475b9f8cf304a44b3` |
| Records | `deb8885bab195b3cc3bdd14ea37687e99b459bdf` |
| PR base | `5bcf11aaf08963ab33ce608ea7509e7403e4351a` |
| Trial-merge campaign head | `4a09f3993eb9344fc5714610e41ab141a0144db8` |

The auditor verified all pack, bundle, source and archive hashes, re-derived the timing argument,
checked the reader repair and the rule-10 evidence (zero touched-declaration failures; 311 untouched
failures matched at base plus the F3 docstring-only case), and ran independent model checks of the
word formulas. It did not recompile; compiler results are verified archived results.

## N1 (note): one additive dependency difference in the trial merge

Confirmed and explained. `TCSlib/Cryptography/Foundations/Negligible.lean` differs between the PR
head (`5e6d2c9e…`, the PR base's version) and the trial-merge build (`56dc45fc…`) by one appended
theorem, `Negligible.comp_of_le`, added to the campaign by #284 (commit `392e2ee9`, merged at
`4a09f399`). It is not part of #286, and the padding proof does not use it. Disposition: recorded
here and in [verification.md](verification.md); no Lean change.

**Clear to merge** — #286 at `a1293a6970b4039a9cf19fd475b9f8cf304a44b3`.
