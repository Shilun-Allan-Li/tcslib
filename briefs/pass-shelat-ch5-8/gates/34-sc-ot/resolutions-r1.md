# Gate 34 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 0 minors, 0 notes.
- **Findings:** `findings/gate34-sc-ot-findings.md`, SHA-256 `9ab967ee0fcf23c393ccefaeb57ad0ff6e397e09553ce492d03a2d9485cbc8e6`. Codex's evidence ZIP was not supplied.
- **Audited head:** `f62a25b3eda099c9cf9371900664752e7b89007d`, records `5d719839`, exchange `a74d1183`.

Codex found no mathematical defect. It checked:
- the efficiency bound;
- Alice's `2δ(n)` at every `n`;
- Bob's predictor identities and the 16 summed instances;
- the freeze (141/0/0);
- the Rule-10 controls, including F-09;
- the builds and the axioms.

| # | Severity | Disposition (ruling Seyoon, 2026-11-15: "fix 01, ledger 02") |
|---|---|---|
| G34-01 | major | **To be fixed by LE-gate34, proof only.** `OT.getD_zero_eq` and `OT.getD_one_eq'` (`ObliviousTransfer/Efficiency.lean:198,203`) will be re-derived from the public `TCSlib.Cryptography.headD_drop`. It is already in the closure, so no import is needed. The headers are kept, and the overlap records are corrected. |
| G34-02 | major | **Ledger debt, DL-48.** `OT.length_ofFn_coins` (`Simulators.lean:210–212`) is a verbatim copy of the public `Composability.NMSim.length_ofFn_coins` (`NonMalleability/Simulation/Rounds.lean:41–43`). Reusing it directly would bring 69 non-malleability modules into the OT closure (78 → 147). The cleanup will promote it to the `NUPPT` layer and re-point both copies. |

**Next:** LE-gate34 runs together with #318's integration rebuild against #316/#317. Then **Gate 34 round 2** checks G34-01's
fix and the disclosure.
