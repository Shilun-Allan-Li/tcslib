# Gate 30 · resolutions, round 1 · CLOSED

Codex's verdict is **CLEAR**: 0 blockers, 0 majors, 1 minor, 0 notes.
- **Findings:** `findings/gate30-prfadv-promote-findings.md`.
- **Audited head:** `5757bc0604527602d790a1a57e9703374ce02c7b`.

Codex confirmed the following:
- the placement beside `prfAdv`;
- the import, which is acyclic and justified (closure 6 → 9 modules, 42 downstream modules gain it);
- the ETT API, which is unchanged;
- that no other unrecorded copy exists. The private `prfAdv_prfReduction` stays deferred.

| # | Severity | Disposition |
|---|---|---|
| G30-01 | minor | **Fixed by LE-gate30, docstring only** (`a24a6313e20a0c3120d457fa4fb0960c72c06312`, tree `6700d281`). The "re-derived here" claim is gone; the overlap note stays as provenance; the sketch now says the theorem is a direct specialization of `TCSlib.Cryptography.prfAdv_eq_expect`. Doc-only check OK, `decls2` empty, 14/14 headers identical, 129/129 rc 0, lint 92/101. Evidence `landing-r1/gate30-le-evidence.zip`, SHA-256 `944de88ab03ec983b82167d35e4fc1cd1aa2ee3db67beb795c235f4a4e194378`. |

**Follow-up from Codex.** DL-44 is not fully discharged until prf-mac re-points its `hadv`. The merged #313/#314 tree
needs an integration build before the second of the two merges.

**Closure (2026-11-15).** The minor was below the gate threshold, so no round 2. Seyoon merged [PR #314](https://github.com/Shilun-Allan-Li/tcslib/pull/314) with LE-gate30 as its head; the merge is `59c2c1fbf8c1bb08f9d191012b7cdd7e15248531`. **Gate 30 is CLOSED.**

Carried forward, outside this gate: prf-mac's local `hadv` re-point (DL-44 F-01, landing edit in progress); the integration rebuilds of #313 and #315 on the merged tip.
