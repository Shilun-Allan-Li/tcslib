# Lamport correctness: one-block coin-length reader proposal

**Unapplied, unchecked proposal.** Explicit source worktree:
`/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.
Frozen HEAD: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.

This patch is the fourth separate Lamport proposal. Its context is the source obtained by composing these existing, unapplied patches **only in memory**, in order:

1. `Lamport-genFun-public-readers.patch`
2. `Lamport-signFun-public-readers.patch`
3. `Lamport-verFun-decision-transport.patch`

No proposal was applied to the library. This invocation changes only the body of the existing local `hρ` proof inside `lamportVerFun_sign`; all headers, premises, helper statements, definitions, algorithms, data fields, remaining proof blocks, docstrings and admissions are preserved.

## Observed diagnostic and cause

Completed seal log:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs/G06Seal_009_TCSlib_Cryptography_Authentication_Lamport.log`.

Probe `1887:4` maps to frozen Lamport source `470:4`, the final `rfl` in `hρ` (source 468–470). Its printed goal is:

```lean
(lamportGen hE).coinLen n = 2 * n * n
```

The previous `List.length_ofFn` step already exposes the coin length correctly. The failing `rfl` then relies on reducing foreign `NUPPT.coinLen` and the uniform-machine constructor/projection. The public reading equations eliminate both foreign reads.

## Exact replacement and API route

```lean
  have hρ : (List.ofFn rg).length = 2 * n * n := by
    simp only [List.length_ofFn, NUPPT.coinLen_eq, lamportGen,
      NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
```

The route is:

- `List.length_ofFn` reduces the list length to the finite domain's cardinal parameter, `(lamportGen hE).coinLen n`.
- Public `NUPPT.coinLen_eq` (`Complexity/Randomized/PPT.lean:163`) reads it as `(lamportGen hE).coins.eval n`.
- Owner-local `lamportGen` (`Authentication/Lamport.lean:371–372`) exposes its application of `ofPolyTimeUniform` with coin polynomial `.mul (.mul (.const 2) .var) .var`.
- Public `NUPPT.coins_ofPolyTimeUniform` (`PPT.lean:393–394`) reads that polynomial without unfolding the foreign machine constructor.
- Public `PolyExpr.eval_mul`, `eval_const` and `eval_var` (`Randomized/PolyExpr.lean:120,111,114`) compute exactly `(2*n)*n`.

Every explicitly listed foreign name is a theorem. The only explicitly listed definition is `lamportGen`, owned by the same file. No explicit `NUPPT.coinLen`, `NUPPT.ofPolyTimeUniform`, `PolyExpr.eval` or Core/Mathlib definition is unfolded. `NUPPT.Coins` remains the existing notation abbreviation; the binder/type is unchanged. No helper-header transport, premise, public API or algorithm change is needed for this local natural-number equality.

This edits **one existing tactic block** and creates no new block; the source's `:= by` count is unchanged. It does not rewrite the surrounding correctness proof.

## Fingerprints and static checks

| Stage | SHA-256 of Lamport source |
|---|---|
| Frozen library | `91dcee4158e54b53372ea573067d8bb08576f73f2b4c08af2889c80d0eebd391` |
| After proposal 1 in memory | `00c992722bf74791be20bd6d6caf35e322c346be27d7f65c97ad3b81b33bc7b7` |
| After proposals 1–2 in memory | `8812be18ab448ff11d1c4f8a8ed0ba995831618780580d724a665f9a437ae09b` |
| After proposals 1–3 in memory (this patch's base) | `d735ef6270bb03ef108adff3a9f6e2b2495b34a27d000bfb12c3a9ca20ef676d` |
| After all four proposals in memory | `7d62658b917225a4e13e75039221eefe628facc6c9ddbe7bb72c30fc0ab81011` |

Patch SHA-256: `ff6425e2abf388147808c946e425e485bd135d1c80aedfb65dcf64fda2f9a05a`.

All three earlier patch contexts matched exactly in memory. The new replacement matched once, and splitting before/after around that exact block confirms all other bytes are unchanged relative to the composed base. The real library retained the frozen fingerprint.

## Required native confirmation and limits

Root should apply the four proposals in order after the source freeze is released, check Lamport through its authorized serial method, then rerun the same whole-file seal with installed-status verification and the associated axiom/explicit-list checks. The hρ diagnostic should disappear through the published readers; the other three proposals remain independently unchecked, and no full-module seal pass is claimed.

If this small rewrite does not close, isolate the printed `coinLen` equality with precisely these public equations in root's native environment; preserve the theorem and coin type. No broader simp, constructor unfolding or header relaxation is proposed.

No Lean/cache, apps, Git writes or library edits occurred. Only the requested ignored proposal files were saved.

**Not yet clear to merge — all four Lamport proposals are unapplied and require root's native replay/seal.**
