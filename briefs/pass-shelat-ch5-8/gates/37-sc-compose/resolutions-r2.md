# Gate 37 · resolutions, round 2 · CLOSED

Codex: **CLEAR**, 0/0/0.
- **Findings:** `findings-r2/gate37-sc-compose-r2-findings.md`, SHA-256 `81b6a2feee121b4c6f5de6f5046621e17285431c0e4a098e291e26583e9f110e`.
- **Audited:** head `4bd2d80bfb58fab5243c66c9f1a697a30b533756`, records `4de7ff85`, exchange `f4287c3c`.

| # | Round 1 | Round 2 |
|---|---|---|
| G37-01 | major | **Closed.** The proof is `CommitmentLemmas.encodeMsgs_append a b`, and the header is byte-identical. |
| G37-02 | major | **Closed.** The proof is `CommitmentLemmas.length_encodeMsgs_le l c h`, and the header is byte-identical. |
| G37-03 | minor | **Closed.** All 20 formulas are complete and correct, and none ends in `…` any more. |

**The `splitCoins` side effect is accepted.** `composeCoins_fst` and `composeCoins_snd` keep their types up to definitional equality,
and `composeCoins` keeps its body. Removing the qualifier gives back the round-1 `Runs.lean` code byte for byte. No printed-type probe or
fresh `Runs` seal is needed.

Codex also confirmed:
- The import is acyclic and adds 47 modules.
- All six merge orders of #324, #326 and #327 give the built tree's `TCSlib` and `audits` subtrees.
- The seals, controls and axioms are as recorded.
- No new duplicate (20,722 theorems scanned).

**Gate 37 is CLOSED.** Merge condition: merge #324 after #326 and #327.
