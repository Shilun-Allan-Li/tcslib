# Yao: typed OT call-header reading proposals

Two separate unapplied, zero-new-tactic-block repairs for `yaoHybrid_callA` and `yaoHybrid_callB` in `TCSlib/Cryptography/SecureComputation/Yao.lean` (original source 627–634).

- Frozen Git context: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
- Frozen source SHA256: `d7d42232e9b74a02c2c24db0df85daa53f2b0c3e310f6e5e1afa7620441c3310`.
- Prior codec-delegation patch SHA256: `df8ad758103ae54ecaa42fdfc5c7ca889665459a1b9437372eeda47e4c18e976`.
- Input after applying codec delegation only in memory: `c82900a901d5cb40edadc6b6968f8e48a1d3acc5752c10fc02e5c32b6b932bfa`.
- Alice patch SHA256: `84cb220ccc7c6d7099bee5591354c893f5a2e11fb38a931f77b5b363d0f21a5a`.
- Intermediate source SHA256 after Alice: `491087509622acf60c96d1014189d5cfbbbd396af3644bcc56debc890696b214`.
- Bob patch SHA256: `acb5dbebe258635557923797c60569bdc0f6125e6635179ed196ac993ba8b599`.
- Combined proposed full source SHA256: `c2bf5ceecf9e2361971b8e2037ced67d28627e4b49a46addd4326810343230ac`.

Apply order for later root checking: codec delegation, Alice call header, Bob call header. The codec patch was consumed only as data by a strict in-memory unified-diff parser, checking every context line and hunk count. No codec proof was edited or executed here, and the codec proposal's independent verification limits remain as recorded by its author. The current mutable library file was not used as a patch base or written.

## Precise diagnostic and authorization

Valid V3 seal 034 reports original source 628 and 634 (probe 678 and 684): a `c : Fin 2` or `c : Fin 1` is passed to a projection expecting `Fin (otFunctionality.inA.eval n)` or `Fin (otFunctionality.inB.eval n)`. These are statement-elaboration errors before the existing `rfl` body. Merely replacing a proof term cannot repair the original literal statement under the seal.

Root explicitly authorized an explicit `Fin` transport in both unissued Gate06 helper headers, preserving every input/equation and adding no hypothesis, as with the prior helper-header repairs. The external S2 candidate freeze is unrelated and untouched. This authorization allows the necessary source-spelling change in each LHS; it does not authorize a different logical claim.

## Public term route and unchanged claim

`otFunctionality_inA` in `SecureComputation/Defs.lean:202` states `otFunctionality.inA = PolyExpr.const 2`; its Bob analogue at 205 uses 1. Applying `congrArg (fun p : PolyExpr => p.eval n)` and composing with `PolyExpr.eval_const 2 n` or `PolyExpr.eval_const 1 n` gives the length equality. `Fin.cast` of its symmetric equality sends each original index into the typed OT input domain.

The parameters remain exactly `(c : Fin 2)` and `(c : Fin 1)`, and the RHS formulas are unchanged. The cast preserves `c.val`. Thus Alice still returns the same selected key bit for every original two-bit index, and Bob still returns the same input choice for every original one-bit index. The casts merely state the canonical identification previously supplied by foreign definitional reduction. Both original `rfl` proof terms remain byte-identical: the owning `yaoHybrid` fields and core `Fin.cast` value projection compute the same formulas. No foreign ordinary definition is unfolded in a tactic list or proof; approved `PolyExpr.eval` notation is read through its existing public lemma.

`HybridProtocol.callA` and `callB` are structure projections; no `HybridProtocol.callA_eq` or `callB_eq` exists in the frozen/current `Hybrid.lean`. No new owner reader is needed because the OT field readers and polynomial evaluation readers already provide the required index identification. No new host/helper definition, premise, admission, or tactic block is added. The only statement spelling changes are the explicitly authorized LHS casts; binders and logical equations are preserved.

## Callers and later blocks

A source search found no direct uses of these two helper names beyond their declarations and module prose. Their existing uses in any future proof will need to supply the same cast (or rewrite through its canonical length equation) when selecting an OT input bit. The separate `yaoHybrid_answersB_getD` proof at original 746–765 uses the raw call projections directly, rather than these helper names. Its observed `outB.eval n = 1` issue at 750 and later typed applications of OT input/output readers still need their own invocation; these patches do not repair that proof. The `yaoMain_outV`, `yaoMain_outP`, and hybrid-HBC errors are likewise outside this proposal.

## Static checks and limits

Each diff is confined to its one helper statement, with its original proof term and all other source bytes unchanged relative to its in-memory input. Both diffs replay exactly in memory. The two repairs add zero `by` blocks and preserve the admission census and all algorithm/data bodies. No library/Git/evidence mutation, Lean/cache/build command, computer app, or native process occurred. The proposed casts and `rfl` elaboration remain uncompiled; root must apply/check separately under native and sealed checks.

**Ready to run**
