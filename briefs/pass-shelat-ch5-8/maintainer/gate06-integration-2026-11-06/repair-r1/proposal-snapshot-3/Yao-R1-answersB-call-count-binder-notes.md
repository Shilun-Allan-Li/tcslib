# Yao R1: normalize the call-index binder before the flattening rewrite

One unapplied follow-up for the existing `yaoHybrid_answersB_getD` proof (current 717–730), based on the **current integrated source**, not an earlier e9/intermediate proposal.

- Source: `TCSlib/Cryptography/SecureComputation/Yao.lean`.
- Required current source SHA256: `7c833ef63102f50483ad73202637cb5784cf5265b7e9195a33e6e2a7d7471396`.
- Proposed full source SHA256, memory only: `5c14ffab999ff4814474f07937b9f336a2fd07fe2024740bf3f5c2a54449d2c4`.
- Patch SHA256: `a985959ed9baca69e577f3bfe8cbed2e5097c4f4581d07634502163b52b05c6f`.

## Observed root

Read-only log:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/repair-r1/native/Yao-public-readers-r1.log`
SHA256 `88f7a381cd7806e2907ab3a0475d5103d5821769d577dde2eb4171638c1b1dda`.

The native error at current source 728 is the rewrite by `h`. Its displayed pattern and target look identical, but their `List.ofFn` binders differ: the supplied flattening theorem is specialized to `Fin (Y.inB.eval n * n)`, while `HybridProtocol.answersB_eq` exposes `Fin ((yaoHybrid Y E₁ E₂).calls.eval n)`. The call-count polynomial is defined in this same file as `mul Y.inB var`; default rewrite matching does not normalize that hidden binder enough here.

## Minimal one-block repair

First apply the public `HybridProtocol.answersB_eq` alone. Then use a `change` step to display the resulting list explicitly with the arithmetic `Fin (Y.inB.eval n * n)` binder. This step reads only the owner-local `yaoHybrid` call-count field and approved polynomial evaluation notation; both sides already contain the same public expansion of `answersB`. It does **not** recover `answersB` by reading its foreign body.

The existing `h` now has the same explicit binder as the target. The rest of the public list, typed-OT point, callA/callB, and `yaoCall_finProdFinEquiv` rewrites are unchanged, followed by the existing Boolean cases. No arbitrary foreign definition unfold, new length assumption, helper theorem, extra Fin transport, or new tactic block is introduced. All original inputs, including vacuous zero-size cases, remain quantified as before.

## Static checks and limits

The diff changes only this one existing proof body and preserves its header and every byte outside it relative to the required current snapshot. Algorithms, data, security premises, admissions, and tactic-block count are unchanged. The source SHA was rechecked before writing the patch/notes.

Only these two unapplied artifacts were written under ignored Gate06 repairs. No library/Git/evidence mutation, Lean/cache/build command, computer app, or native process occurred. The proposed local definitional conversion and subsequent rewrite applicability remain uncompiled; root must apply/check separately. This is neither a native pass nor final collector/seal evidence.

**Ready to run**
