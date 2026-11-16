This is the landing PR of the Pass–shelat fill `sc-yao` (`PassShelatChapter5-8Plan.md`, prong B). It proves the two frozen Yao targets in `SecureComputation/Yao.lean`, which are Yao's garbled-circuit protocol [PS10, Protocol 162.6] in the bit-transfer (OT) hybrid model:
- `yaoHybrid_polyTime`: the hybrid protocol is polynomial time;
- `yaoHybrid_simulators`: the honest-but-curious simulators for Alice and Bob [PS10, Theorem 163.7].

`yaoHybrid_hbcSecure` follows from the two targets. The real protocol, `yaoProtocol_hbcSecure`, follows by composition with sc-compose's `HybridProtocol.hbcSecure_compose` (#324, merged). **On the merged tip it uses only the standard axioms.**

**Head:** `355a0288d56290e8c984228cbc1824187029e456`. **Base:** `cryptography/pass-shelat-ch2-4`, from the tip `f9fda8fe`. Since then the branch has gained #327 and #324 (`201bf57a`) and records only. Neither touches this PR's files, and the merge is clean.

## Changes (70 files against `f9fda8fe`)
- `Yao.lean`: only the six approved regions change, plus LE-title's title line. The file has 1195 lines, within the SY-2 waiver of 1,200.
- `Circuits/Uniform.lean`: seven SY-3 encoding readers, each a formula docstring with an `rfl`/`Iff.rfl` proof.
- The hub `Yao/HybridProof.lean` and 67 helpers under `Yao/HybridProof/`. Every line is at most 100 characters.
- `DAGCircuit.lean` is unchanged against the tip.

## Commits (15, all SSH-signed)
- The worker's 8 commits (Codex delivery, exchange `47c38c47`), rebased onto the tip with authorship kept.
- **Review landing edits:**
  - LE-bullet `13690d2e`;
  - LE-reuse `81d526d8` (SY-F05);
  - LE-title `bd7832d7`;
  - LE-doc `e9b03c43` (SY-F04, docstring-only).
- **Gate 42 round-1 landing edits:**
  - **LE-reuse-2** `26f0b77b` (G42-01): `RunWithHost.acc_poly` now derives from the public `StateLoop.MajLoop.acc_poly` through the two published readers. Proof-only; the docstring discloses the reuse.
  - **LE-refs** `3e99eb80` (G42-02): full `[AB09]` and `[BMR90]` bibliography entries.
  - **LE-steps** `355a0288` (G42-03): step comments in the six long proofs. Comment-only.

## Checks
- **Integration on the records tip.** Merge M of the tip with `e9b03c43`:
  - **772/772** modules rc 0, with 0 `error:`/`error(`, through root `TCSlib` and both `Checks`;
  - state check 1410/1410;
  - admissions **229 → 227**.
- **Gate 42 landing edits.** M′, M with `355a0288`: 20 modules rebuilt, 20/20 rc 0; state OK; `acc_poly`'s new body elaborates.
- **Axioms**, standard three only on M and M′:
  - `yaoProtocol_hbcSecure`, with 0 `sorryAx` users in its closure;
  - `yaoHybrid_hbcSecure`, `yaoHybrid_polyTime`, `yaoHybrid_simulators` and `yaoSeed_good_whp`;
  - `hbcSecure_compose` and all ten `otProtocol_*`;
  - `RunWithHost.acc_poly`.
- **Rule 10:**
  - `Yao.lean` seal A has 0 errors. Seal B has 24 errors in 9 declarations, all `PolyExpr.eval` conversions or cascades; this matches the review byte for byte.
  - `Uniform.lean`'s 4 errors are inherited from the tip.
  - Helpers: canonical coe-A seals pass on all 68.
  - `RunWithHost` after LE-reuse-2: coe and strict, A and B, all have 0 errors.
  - Paired controls are ALL_OK; the explicit-unfold scan finds 0 foreign unfolds.
- **Lint:** no new FAIL.

## Findings
- **Review r1** (ACCEPT WITH LANDING EDITS), with Seyoon's rulings:
  - SY-F01 is confirmed.
  - SY-F02 is ledger debt, DL-51.
  - SY-F03 is ledger debt, DL-49 extended.
  - SY-F05's remaining pair is ledger debt, DL-52, re-pointed after this merges.
- **Gate 42 round 1** (Codex, at `e9b03c43`): **HOLD**, with 0 blockers, 1 major and 2 minors. It found no mathematical gap. G42-01 to G42-03 are resolved by the three landing edits above (`briefs/pass-shelat-ch5-8/gates/42-sc-yao/resolutions-r1.md`).
- **Gate 42 round 2** at this head: being staged.

The evidence is in `briefs/pass-shelat-ch5-8/fills/sc-yao/final-r1/`: `review.md`, `review-evidence.zip`, `post-merge-addendum.md`, `rulings.md` and `integration-tip/`. Seyoon merges.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA