# Gate 03f1 (discrete log, its hard-core bit, ElGamal): round 1 resolutions

- **Round:** findings `findings/gate03f1-findings.md`, SHA-256 `72909f86e53f745a24af86d23704e1eba2929189f6ab9497a67c504065203b4b`; pin `0c348ff9`. **0 blockers, 1 major, 2 minors**; the 21 admissions 15 (a), 6 (b), 0 (c). Review `review/gate03f1-review.md`: all true; `fullDLCollection_hardCore` provable as stated. Ruling R-03f1-1 (A): keep `hbig`.
- **Repair:** the gate 03 repair batch, PR [#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206) (head `73751f5747d8c0a57aba9939cac8bb16f87ba2ba`, merged by `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; evidence `evidence-repairs/03-batch/`), plus the records commits of 2026-11-06.

| Finding | Severity | Resolution |
|---|---|---|
| #1 | major | **Fixed** (#206, item D). `fullDLCollection_hardCore`'s sketch is replaced by the review's §1.4: `n²` coins for `t`, `n²` plus A's coins per trial, `T ≤ 16n^c`, success `≥ 3/(256 n^{2c}) − (1 + 16n^{2c+2})·2⁻ⁿ`, and the binary numeral of `8n^c` in the inverter's advice. Docstring only. |
| #2 | minor | **Fixed (records).** Claim-62.2's inventory rows point at `Rabin.lean` · `rabin_symmetry` (audited at 03f2). |
| #3 | minor | **Fixed.** `ElGamal.lean`'s history of the run-3 DDH repair (P8-1), with the review's texts. |
| M1 | (review) | **Fixed (docstrings; ruling R-03f1-1 (A)).** `hbig` is described as "used, a convenience, dispensable" at `DiscreteLog.lean` and `ElGamal.lean`; the statements keep it. |
| M2 | (review) | **Fixed.** `sampleBelowL_eq_rejectBlocksL` (`DiscreteLog.lean`), with `rejectBlocksL_eq` beside its definition (`Concrete.lean`) so that no other file's definition is unfolded. `statClose_sampleBelowL`'s sketch derives it from `statClose_rejectBlocksL`; the DL fill brief fills it as a corollary. |
| M3 | (review) | **Fixed.** The stale "requested shared primitive(s)" wording cites `H.size` and `H.sub`. |
| M4 | (review) | **Recorded.** Prong A's `DLHash.lean` also uses `expGenFun`, `expSampleRaw`, `expEval`, `ExpValid`, `dlM`, `dlP`, `DLHard`, `expF_injective` and `statClose_sampleBelowL`; no fix changes them. |
| Notes | note | No change. |
