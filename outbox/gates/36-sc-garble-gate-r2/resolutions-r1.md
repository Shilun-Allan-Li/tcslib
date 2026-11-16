# Gate 36 · resolutions, round 1 · HOLD → round 2

Codex's verdict is **HOLD**: 0 blockers, 1 major, 0 minors, 0 notes.
- **Findings:** `findings/gate36-sc-garble-findings.md`, SHA-256 `b14b8860d26206cb6016cc00f7b9a376bed619a0ac94ffbc2aaffe0889c1f4fb`. The companion ZIP was not supplied.
- **Audited head:** `cd9a48438c2a6548fe9e246ce569be57c9df96b3`, records `fb18d199`, exchange `ab34c528`.

Codex found all seven targets and B2 correct against [PS10 §§6.2.2–6.2.3], with every edge case covered. It also confirmed:
- `specialScheme_multiMessageSecure` is proved directly from D4;
- the B1 maximization keeps the empty-set convention;
- Gate 27 obligations (1)–(6) are met;
- SG-1 removes exactly six helpers, and both controls behave as specified;
- the stricter `Yao.lean` rule holds;
- the SG-F01 reader adds exactly nine lines;
- the seals and controls verify, and seal B's nine new errors are the disclosed `PolyExpr.eval` ones;
- the axioms are standard.

| # | Severity | Disposition |
|---|---|---|
| G36-01 | major | **To be fixed by LE-gate36, a maintainer landing edit.** `SliceReduction.length_le_encodeList` (`SpecialEncryptionMulti/SliceParser.lean:119–126`) re-proves the public `TCSlib.Cryptography.length_le_length_encodeList` (`Asymptotic/BlockEncryptor.lean:53–76`) for the same encoder and domain. The fix removes the new duplicate and points its one use in `slicePost_encode` at the public lemma. It imports `Asymptotic/BlockEncryptor`, which is acyclic and adds 2 modules to the closure. The overlap record is corrected. No frozen declaration changes. |

**Next:** the edit is made on the landing branch, rebased onto the tip (which includes #313), then rebuilt and re-sealed. After that, Gate 36 round 2 runs.
