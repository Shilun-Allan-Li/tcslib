# Yao: typed ideal-OT answers proof proposal

One unapplied existing-proof repair for `yaoHybrid_answersB_getD` (original source 746–765), plus one explicitly authorized, home-local term reader in `SecureComputation/Defs.lean`.

## Contexts and hashes

Frozen Git context: `e9d64158461bfe24ddc88ab885bc4017899b4c16`. Current library sources were not used as patch bases or edited.

- Frozen Yao SHA256: `d7d42232e9b74a02c2c24db0df85daa53f2b0c3e310f6e5e1afa7620441c3310`.
- In-memory Yao input after codec + callA + callB only: `c2bf5ceecf9e2361971b8e2037ced67d28627e4b49a46addd4326810343230ac`.
- Proposed Yao source SHA256: `07a706e5ab0e535adf90b8e9508422897fff7bf2c3ae4e1f9f9eef29fe919e8a`.
- Yao proof patch SHA256: `a4613412cafe9001d416493f854cf0a91f5890de3e2f6ecfb3a1666d142a9ac8`.
- Frozen Defs SHA256: `b761c437034a6d808d09357d6d8a4c1a841d332e1e3d12c707d506cd8c996b51`.
- Proposed Defs source SHA256: `b6a86a5b9f0843642cf3d6a9e3ef05cb34cb4081d24c80a5c139f9cbbdc2452b`.
- Separate owner-reader patch SHA256: `6061db3e8cc5dd2113feceda8b46b0626d19216aca6020e229853c15b718476a`.

The prior three Yao patches were hash-checked and applied only with a strict in-memory unified-diff parser. Their SHA256 values are codec `df8ad758103ae54ecaa42fdfc5c7ca889665459a1b9437372eeda47e4c18e976`, callA `84cb220ccc7c6d7099bee5591354c893f5a2e11fb38a931f77b5b363d0f21a5a`, callB `acb5dbebe258635557923797c60569bdc0f6125e6635179ed196ac993ba8b599`. Other Yao proof proposals were not composed here. Apply the separate Defs owner patch before checking this Yao proposal. At inspection the current Defs bytes also matched its frozen hash; the owner patch is kept separate for root's composition with other owner changes.

## Observed root and necessary typed reader

Valid V3 seal 034 reports source 750 (probe 800): `rfl` cannot establish `otFunctionality.outB.eval n = 1` while the functionality is sealed. Replace it by the equality obtained from `otFunctionality_outB` under evaluation and `PolyExpr.eval_const 1 n`.

Further reads in the same proof were masked by that first error. The first `show` reads the body of foreign `HybridProtocol.answersB`; use its existing `answersB_eq`. The second `show` computes the foreign OT functionality and its input lengths. The existing `otFunctionality_f_snd` reader takes literal `Fin 2 → Bool` and `Fin 1 → Bool` inputs. The sealed hybrid-call functions instead have domains `Fin (otFunctionality.inA.eval n)` and `Fin (otFunctionality.inB.eval n)`, so that fixed-domain reader is insufficient for a direct typed application.

Root authorized a public home-side term point reader beside `otFunctionality_f_snd`, with full typed input/output domains, public-reader `Fin.cast` identifications, no hypotheses, and no simp attribute. The separate owner patch adds exactly `otFunctionality_f_snd_apply`: for arbitrary typed inputs `a`, `b` and any typed Bob output index `j`, `(otFunctionality.f n a b).2 j` is `a` at the cast two-bit index selected by `b` at the cast zero one-bit index. The length-cast terms are exactly those of the earlier callA/B proposals. Its body is owner-local `rfl`; no helper definition or new tactic block is added. Existing owner declarations, data, algorithms, and headers are preserved.

## One Yao proof repair

After obtaining the flattening identity with the public outB length equation, rewrite through `HybridProtocol.answersB_eq`, that flattening identity, the existing index arithmetic equality and list reader, the new typed OT point reader, the repaired `yaoHybrid_callA`/`callB` interfaces, and `yaoCall_finProdFinEquiv`. The remaining Boolean case split is unchanged in substance. Neither foreign-body `show` step remains.

The theorem header and every input/equation are unchanged. The proof handles all original parameters, including vacuous `Fin 0` cases, without a new positivity or other hypothesis. The existing private flatten/list lemmas are reused; no host or duplicate algorithm is introduced. The mathematical sketch remains accurate.

## Static checks and limits

The Yao diff changes only this one existing proof body; its tactic-block count and admission census are unchanged, and every byte outside that proof is identical to the in-memory input. The owner diff adds only one formula-documented theorem beside its owning definition and readers, with a term `rfl` proof and no `@[simp]`. Both diffs were replayed in memory and reproduced their proposed sources exactly. All data algorithms, security premises, admissions, and existing declaration headers remain unchanged.

Only these two patch artifacts and these notes were saved under ignored Gate06 repairs. No library/Git/evidence mutation, Lean/cache/build command, computer app, or native process occurred. The new owner term's elaboration, rewrite matching across the point/call readers, and composed source remain uncompiled and require root's native and sealed checks.

**Ready to run**
