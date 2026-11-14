# Gate 24 · resolutions, round 1 · round 2 to follow

Codex's verdict is **HOLD**: 0 blockers, 1 major, 2 minors and 0 notes.
- **Findings:** `findings/gate24-dl-crh-findings.md`, SHA-256 `f29e4cb936dff2a470c58ccd405f6f37d755297eeefdc462e8bfd99494a4b689`.
- **Audited head:** `649c4888f23fbb9df71d555e952d1149a0aaa00b`.

| # | Severity | Disposition |
|---|---|---|
| G24-01 | major | **Fixed by LE-reuse** `d356381aadc350860f9a0e97123e84d9aefa585b` (tree `c7b77d28fa11c95a00789102e8d9410fc931bf63`), proof only. `inputWord_take` now reads `take_ofFn_castLE`, and `inputWord_split` is `ofFn_eq_init_append`, which also clears that DL-41 item. Re-audit in round 2. |
| G24-02 | minor | **Erratum** in `fills/dl-crh/final-r1/review.md`, Content step 2. A collision with *equal* selectors is impossible; the review had said *different*. The Lean proof and the target's sketch were already correct. |
| G24-03 | minor | **Erratum** to the pack, ruling 3. FAIL lines are identical at the head and the tip, but two `DiscreteLog` WARN lines change (`1192 → 1212` lines; missing readers `6 → 5`, after `expSampleRaw_eq`). The counts stay at 92 FAIL / 102 WARN. These two WARN changes are the accepted ones. The pack is pinned, so the correction is recorded here. |

## LE-reuse (`d356381a`)

**What changed.** Only `Hashing/FromDiscreteLog/Encoding.lean`, which grows from 199 to 201 lines:
- `inputWord_take := (take_ofFn_castLE (Nat.le_succ n) x).trans (congrArg List.ofFn (funext fun _ => congrArg x (Fin.ext rfl)))`.
- `inputWord_split := ofFn_eq_init_append x`.
- A new `import TCSlib.Cryptography.Asymptotic.ReductionSupport`. It is a real addition: it brings `ReductionSupport`,
  `Foundations.Negligible`, `Pseudorandom.Generators` and `Pseudorandom.Indistinguishability` into `Encoding`'s
  closure. `Authentication` and root `TCSlib` already import them, and none of them imports a unit module, so there
  is no cycle.
- The names, types and docstrings of both theorems are byte-identical.

**Statements.** decls2 against `649c4888` is empty, and all 198 headers are byte-identical.

**Build**
- On `dl-oleans`, the same 22 modules as the LE-doc build give rc 0, through root `TCSlib` and
  `audits/pass-shelat/Checks`.
- Only `Encoding`'s olean changed.
- The whole-tree check covers 1207 modules: OK.

**Rule 10**
- `Encoding.lean` passes seals A and B, strict and coe. Its request sets grow by the 24 rows that come from the newly
  imported modules; every earlier row is unchanged.
- Paired controls (`padFin`, `splitBits`, `PolyExpr.eval`): ALL_OK.

**Axioms.** `dlHash_crh` uses only the standard three.

**Lint.** 92 FAIL / 102 WARN, with the same FAIL and WARN lines as before.

**Restore.** `dl-oleans` is back at the base snapshot `457ba704…`.

**Evidence.** `landing-r1/gate24-r1-evidence.zip`, SHA-256
`6c1802139817f3fc033a50ecec1e9a8ff6f953bccad5b82b02f4c9bddb94fa22`. The patch is in `landing-r1/`.

**Next.** A trial-merge build onto the records tip (which now includes #308 and #309; the merge is conflict-free,
tree `e0415be6`) is running. After it, round 2 is staged for Codex.
