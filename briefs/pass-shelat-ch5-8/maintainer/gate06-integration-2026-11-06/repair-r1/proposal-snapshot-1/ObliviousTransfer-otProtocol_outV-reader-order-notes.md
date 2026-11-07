# ObliviousTransfer: output-correctness tape rewrite proposal

One unapplied existing-proof repair for `otProtocol_outV` in `TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean` (original source lines 260–334).

- Frozen Git context: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
- Frozen source SHA256: `8486698f1624b8bca32baffbc53f7c3f754de6919df367e4245e48d9a3c28e09`.
- Proposed full source SHA256 (memory only): `54744eb63b40489fcd4a700f8f7089b5d167c857fc40fd3157eee558acfdcac1`.
- Patch SHA256: `b1faa50f47fa7207dd67ba0246d6820ab95a4316ab854e2b0d0139408fa6d959`.

The current mutable library file was not used as the patch base or edited.

## Valid V3 evidence and root

Read as data:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_031_TCSlib_Cryptography_SecureComputation_ObliviousTransfer_HarnessV3.log`

Log SHA256: `48f872bebd44a58c10490b72de18cd4665ab989ed99378f1d867488ac99b4d44`. The seal installation/EOF counts are 952 requested, 952 active, zero already irreducible, all verified. The generic result records two source diagnostics, exit 1, no fresh object, and unchanged probe SHA256 `7e95ba4492ff50d3cfcf79a790df8c007111662800ee4a433a05a4a444c12dca`.

Original source 284 maps to probe 334. Its `rw [hAr, hBr]` cannot find `List.ofFn rA₀`. The logged target already contains the cast functions `fun i => rA₀ (Fin.cast ... i)` and `fun i => rB₀ (Fin.cast ... i)`, which are precisely the existing local typed tapes `rA` and `rB`. Thus the raw tape-list equations are being requested after the dependent simplification has changed the representation. This diagnostic does not show a false correctness statement or a need for a stronger evaluator premise.

## Minimal repair within the existing proof

Apply `Protocol.outV_eq` and `Protocol.transcriptWith_eq` first. At that point the two unmodified raw tape lists occur explicitly in the output equation and `exec`. Immediately rewrite them with the existing `hAr` and `hBr`, whose proofs are the public `List.ofFn_congr` contract. Then run the existing five-move simplification using only the same-file `otProtocol`, `otSender`, `otReceiver` and the public `exec_succ`/`exec_zero` equations.

This changes only the order of the existing reading and computational steps. The canonical typed-tape construction, its explicit `Fin.cast` operations, its length equations via public `Strategy.coinLen_eq` and `NUPPT.coinLen_eq`, and the rest of the inverse/XOR argument remain exactly as written. The two protocol readers are in `ZeroKnowledge/Interaction.lean` (`outV_eq` at 435, `transcriptWith_eq` at 410); `List.ofFn_congr` is in the imported Mathlib `Data/List/OfFn.lean:47`.

No missing owner reader, helper definition, new tactic block, new premise, or algorithm/data change is needed. Review of the remaining same proof found the foreign reads already use published `runAt_eq`, collection fields (`sample_spec`, `f_perm`, `inv_spec`), `Collection.apply_of_decD`, and the inverse/pairing equation lemmas. The explicit unfolds of OT constructions are same-file definitions and remain allowed.

The canonical evaluator specification `henc` is preserved, as is the local decodable-input consequence `hspec` derived with `Collection.apply_of_decD`. This proposal does not erase an arbitrary evaluator relation or infer a bare-hard-core route. All `hH`, `henc`, `hT`, and `EnhancedHardCore` declarations/premises elsewhere in the file remain byte-identical, and every admission is unchanged.

## Separate HBC root — diagnosis only

Original source 656 maps to probe 706. The direct tuple tries to construct foreign sealed `HBCSecure`. The existing public `hbcSecure_iff` in `SecureComputation/Defs.lean:184` exposes exactly the conjunction of polynomial time and the two simulator witnesses with uniform negligible bounds. Its reverse direction is the appropriate constructor interface. The current witnesses and `otProtocol_simulators` application already state that contract, with their canonical evaluator and cost assumptions retained. No HBC proof code is proposed or changed in this invocation; it remains a separate existing-proof repair.

## Static checks and limits

The diff is generated from the exact frozen Git bytes and changes only this one proof body (three old lines replaced by two). Its header and all bytes outside this proof are preserved, as are its tactic-block and admission counts. No proof sketch update is needed because the mathematical strategy is unchanged.

Only this patch and these notes were written under ignored Gate06 repairs. No library/Git/evidence mutation, Lean/cache/build command, computer app, or native process occurred. The reordered rewrites remain uncompiled; root must apply/check them separately, including the rest of this previously interrupted proof.

**Ready to run**
