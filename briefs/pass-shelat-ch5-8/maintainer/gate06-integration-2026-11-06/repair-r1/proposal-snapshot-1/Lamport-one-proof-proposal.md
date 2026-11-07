# Lamport: one-proof public-reader repair proposal

**Unapplied, unchecked proposal.** Frozen source head:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`.

Only the existing `polyTimeComputable_lamportGenFun` proof is proposed for editing. The patch
replaces its final `convert h using 1` with pointwise transport through the public
`PolyTimeComputable.congr` theorem (`Complexity/Randomized/Closure.lean:101`). The equality
uses `lamportGenFun_eq` (owner-local function reader), foreign `blockState_eq`
(`Asymptotic/BlockEncryptor.lean:80`) and `Function.comp_apply` (a Core theorem).
`blockEncFun`, `NUPPT.inParam` and `NUPPT.inCoins` remain opaque, identically applied on both
sides. No import, helper, header, logical premise, algorithm, data field, admission or new
tactic block is added. Every source byte outside this existing proof is preserved.

## Completed-log mapping and roots

Input: `evidence-rule10-r2/runs/G06Seal_009_TCSlib_Cryptography_Authentication_Lamport.log`
in the main campaign records, inverted through `seal-manifest.json`'s source line map.
The run reports RC 1, four error diagnostics, unchanged probe source and no fresh object.
The existing `sorry` warning is separate from those four errors.

| Probe line:column | Frozen source | Declaration / block | Root and disposition |
|---|---:|---|---|
| 1719:83 | 302 (final conversion at 308) | `polyTimeComputable_lamportGenFun` | The compositional witness builds nested `pairEncode`, while `lamportGenFun` wraps those fields in foreign `blockState`. The final `convert` relies on its reduction. **Only repair proposed here:** explicit pointwise equality through `blockState_eq`. |
| 1728:81 | 311 (final conversion at 320) | `polyTimeComputable_lamportSignFun` | Same foreign `blockState` conversion beneath the block encryptor and tuple flattener. Flagged for a separate invocation; no signer proof patch written. |
| 1779:42 | 362 (local `h₃`, lines 363–365) | `polyTimeComputable_lamportVerFun` | The equality-test witness leaves an unresolved pointwise `decide` equality after `convert` and simplification. The printed sides look identical; hidden conversion/decider arguments are not exposed by this log. `blockState_eq` is already present at this site, so it must not be dismissed as a missing-reader copy of the first two errors. Genuine source diagnostic, exact minimal cause not isolated; no verifier proof repair written. |
| 1887:4 | 470 (`hρ`, lines 468–470) | `lamportVerFun_sign` | The final `rfl` reduces foreign `NUPPT.coinLen` and the uniform-machine constructor to obtain `2*n*n`. A separate repair should use `NUPPT.coinLen_eq`, the owner-local `lamportGen` equation, `NUPPT.coins_ofPolyTimeUniform` and polynomial evaluation lemmas. No correctness proof or helper-header change written here. |

The maps land in original source, not seal installation commands. The selected generator
repair does not claim to fix the other three diagnostics, nor the whole sealed module.
No coin transport or helper-header adjustment is needed for this selected function proof.
Later native-coin repairs must retain the same typed equations, using public transports if
required rather than adding a premise or changing the algorithm.

## Static checks and evidence limits

- Frozen Lamport source SHA-256: `91dcee4158e54b53372ea573067d8bb08576f73f2b4c08af2889c80d0eebd391`.
- Proposed file SHA-256 after applying only this patch: `00c992722bf74791be20bd6d6caf35e322c346be27d7f65c97ad3b81b33bc7b7`.
- Executed survey-probe SHA-256: `c4905cb2c4f9828512c4acd6e662e118a7641e50153708258e902a9fa784924a`.
- Header and all bytes outside the selected proof are unchanged. The count of existing
  `:= by` blocks is unchanged. No further proof block is written in this invocation.
- The patch was generated as data; the library remains frozen. No Lean/cache, Git command,
  app, native proof check or seal rerun was used. The proposed term remains unchecked.

**Not yet clear to merge — one proposal is unapplied/unchecked; three other Lamport diagnostics and broader verification remain.**
