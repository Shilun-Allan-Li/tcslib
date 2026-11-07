# Lamport R1: remove dependent tape before coin simplification

Unapplied follow-up to the one existing `hρ` proof block in `lamportVerFun_sign`, current source 472–474. **This patch is based on the current integrated source snapshot, not on the original e9 proposal context.**

- Source: `TCSlib/Cryptography/Authentication/Lamport.lean`.
- Required current source SHA256: `7d62658b917225a4e13e75039221eefe628facc6c9ddbe7bb72c30fc0ab81011`.
- Proposed full source SHA256 (memory only): `ea4425be89a8e557c24f77380f6f3de8ad1dfecddcce533cc531117c858c2d38`.
- Follow-up patch SHA256: `617e67d173cceba85fddc367c46e43497e8d2f8b4f137b86fca917bda167cd4c`.

## Observed diagnostic

Read as data under main R2:
`diagnostic-evidence/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R1_Lamport/runtime-validation.json`
(SHA256 `1bd3a529719bb55ed856bd3c8fe3822bbf10a6abf8ccedcfc9bf8d6e1c70eb0d`) and
`diagnostic-evidence/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R1_Lamport/native/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R1_Lamport.log`
(SHA256 `b582009b203fbbb4fe4ac3fefa4c3218b0c88baffb41539ee574c52e06c27744`).

The diagnostic validation reports a valid **old-row diagnostic harness**, with 1,355 rows installed/verified (1,337 active plus 18 already irreducible), exact EOF verification, and one actual source error at current source 472 / probe 522. The target remains the entire list-length equality. `List.length_ofFn` is reported unused in the current broad simplifier list. The native result exits 1; this is a failure, not a pass or a final-coverage claim.

## Proposed one-block repair

Build the first two equality steps explicitly as terms:

1. `List.length_ofFn (f := rg)` gives `(List.ofFn rg).length = (lamportGen hE).coinLen n`.
2. `(lamportGen hE).coinLen_eq n` gives that coin length as `(lamportGen hE).coins.eval n`.

The `refine` equality chain leaves only `(lamportGen hE).coins.eval n = 2 * n * n` as its subgoal. The dependent function `rg` is absent from that goal before any generator or polynomial simplification. Then the owner-local `lamportGen` definition, the public `NUPPT.coins_ofPolyTimeUniform` equation, and the public polynomial evaluation equations reduce it to reflexivity. The polynomial is `mul (mul (const 2) var) var`, so its readout has exactly the desired association `2 * n * n`.

The core source signature makes `f` implicit, so the first term supplies it by name. This avoids depending on the simplifier's traversal through the type of `rg`, and avoids a separate tactic after a potentially goal-closing native `rw`. No new owner theorem, helper definition, foreign definition unfold, or tactic block is needed. The only explicit definition in the list is `lamportGen`, which is owned by this file.

## Preservation and limits

Only the body of the existing `hρ` changes. Its statement, the enclosing theorem header/premises, algorithms, data, security statements, all other proof blocks, and admissions remain byte-identical to the current input. The number of `by` blocks and admission census are unchanged. Current source bytes were checked again before writing the artifacts.

Only this patch and these notes were saved under ignored Gate06 repairs. No library source, Git state, native object, actual probe, or diagnostic evidence was written, and no Lean/cache/build command or app was run. The equality-chain elaboration and remaining simplifier step are uncompiled proposals; root must apply/check them after its active diagnostic queue. A fresh collector remains required for final gate coverage.

**Ready to run**
