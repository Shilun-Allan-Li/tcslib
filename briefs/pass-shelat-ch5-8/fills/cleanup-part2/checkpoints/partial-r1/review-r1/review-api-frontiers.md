# Partial-r1 API/frontier review

**0 blockers / 1 carried major / 1 minor in this bounded review.** The inline unary-multiplication consumers have a concrete permitted alternative. The other inline-match sites remain unresolved; this review does not certify their repair or prove a permission blocker. The three original PolyTime provider proofs are genuinely outside the worker's proof-edit permission.

Snapshot exchange commit `0c4d4f60203021f3a3b93f88eaf7c9085c6ab885`; reported worker head `03ead73ab38e74621800367c072f6fd3f0f70991`; ancestor `1aa5506f58f77c215e56d24311ec33bd931cacf1`. I read the entire 721-line, 50,978-byte REPORT (SHA256 `dca5f8e5961b83b402a6255ff4afd4273a555e3d04a9f1fb391fa15acdb8b57e`), including Escalations 292–330. Source references below are relative to the immutable `payload/src/`.

## Minor FRONTIER-01: unary multiplication is not established as permission-blocked

REPORT:299–321 says that the anonymous contracts can be identified with consumer functions in only two prohibited ways. That assertion is too broad for the four unary consumers listed there. Existing `Complexity.BinArith.polyTimeComputable_mulU` (`ClassP/BinaryArith/Loops:448`) computes `mulU`, and `BinArith.length_mulU` (444) publishes:

```lean
(mulU (pairEncode a b)).length = a.length * b.length
```

Compose this machine with the existing unary length map. It yields the unary product through published composition and length contracts, without mentioning the anonymous `computesFunInTime_unaryMul` function or matcher. No new reader, data definition, host, public header or hypothesis is needed. Empty strings give the same zero product.

| Existing consumer | Permitted source-level route; not a compiled repair claim |
| --- | --- |
| `EncodingMachines.unaryMul_poly` (`EncodingMachines:88`) | Pair the two unary functions, apply `mulU`, then unary length; use `length_mulU` and `List.length_replicate`. |
| `OneWay.polyTimeComputable_unaryMulPair` (`OneWayLemmas:325`) | Pair both total projections of the arbitrary input first, then the same construction. Malformed inputs still have empty projections and output `[]`. |
| `GGMRed.unaryMul_poly` (`GGMReduction:915`) | Pair the two arbitrary word-valued functions, then `mulU` and unary length. Its conclusion is exactly the product of their lengths. |
| `GI.unaryMul_poly` (`GraphIsomorphism/EfficiencyRep:349`) | Use the total-projection construction and identify it with this theorem's **own existing inline-match header** through congruence and published projection equations, preserving the malformed branch. Do not change that header to the projection formula. |

The single proposal in this invocation is `01-encodingmachines-unaryMul.patch`. It adds the precise Loops import, replaces **one existing tactic block**, and refreshes its obsolete copied-machine proof prose. Header bytes are unchanged. The Loops closure has 44 local modules and reaches neither EncodingMachines nor any Cryptography module, so the new import is acyclic. Source/context/import/old-new proof hashes are in the adjacent JSON. Patch SHA256 `246512efe882b390d7f466bc821f4e07dcc659f602b77a291e55c1b770eb2b42`.

The patch is **unapplied and uncompiled** by this reviewer. The other three routes have no new proof proposal in this invocation. Existing `polyTimeComputable_unary` has its separately reported lower-level seal debt; legally using its published statement does not discharge that debt.

Suggested replacement for the categorical escalation wording:

> The current direct bridge to the inline provider contracts is unresolved. Four unary-multiplication consumers have a concrete permitted alternative through `BinArith.polyTimeComputable_mulU`, `BinArith.length_mulU` and the unary length map; the EncodingMachines proposal remains uncompiled. Other inline-match sites need focused reader/contract analysis. A current type-mismatch diagnostic alone does not establish that a new general theorem is required.

## Other inline-match frontiers remain unresolved

The raw seal logs do show visually identical inline functions failing to unify in `polyTimeComputable_unary`, `polyTimeComputable_lenLe` and EncodingMachines; GGM's stateLoopFun/lookup fail where the foreign inline function is converted to its named data function. These are actual source-frontier observations. They are not evidence that arbitrary case analysis has already closed the sites.

- **stripLast / pairLenCheck:** Build/Primitives already exposes public named `stripLastTM` and `pairLenCheckTM`, with `stripLastTM_computes` (3176; budget `150*(n+1)`) and `pairLenCheckTM_computes` (3054; its exact existing polynomial budget). X12 expressly allows ordinary machine run/case contracts beside existing owners. Assess a complete same-machine/same-budget case-reader route under that permission before classifying every reformulation as a new non-reader theorem. I have not proposed or verified those readers here; preserve existing definitions, original theorem headers, costs and dependencies.
- **pairMapSnd:** the existing private `pairMapTM`/`pairMap_computes` (2603/2945) and `catalogPayload_computes` (2296) give a lower owner to investigate. Determine whether ordinary run readers suffice without promoting/altering the machine or adding a generic FP theorem. No verified repair or new permission is asserted here.
- **iterateFind → GGM stateLoopFun/lookup and Yao yaoRaw:** keep the frozen existing data and public headers. Merely introducing a new named `iterateFind` definition/host or a second general polynomial-time theorem is not automatically ordinary reader work. Existing named-machine run/contract routes should be examined first; if they do not suffice, report the smallest exact API request. I have not established either a legal complete repair or an impossibility. `IterateFind.polyTimeComputable_find` also has separate state-type/predicate/configuration diagnostics; fixing one bridge would not certify its whole proof.

**N4 boundary:** do not treat constructor-discriminant reduction of a sealed foreign matcher as acceptance. The retained first N4 control demonstrates that such reduction can escape the seal. No foreign matcher or generated-equation name is used by the proposed unary route. Case analysis of GI's **own header** using public pair projection equations is a different source situation and does not read that foreign anonymous contract.

## E-FREEZE 1 is an actual permission boundary, not an API absence

Issued `inputs/role-manifest.json` marks `ClassNP/PolyTime.lean` PROVIDER_ONLY; X12 allows new ordinary readers and forbids editing any original proof. The complete original headers/proofs of these three declarations are byte-identical to the ancestor:

- `Complexity.polyTimeComputable_id` (current source 90–94).
- `Complexity.PolyTimeComputable.output_length_le` (103–109).
- `Complexity.PolyTimeComputable.comp` (161–172).

Their use of a foreign `ComputesFunInTime` hypothesis as a function has an ordinary mathematical repair through existing `FinTM.computesFunInTime_iff` (Finite:289). Availability of the reader does **not** grant permission to edit these provider proofs. None of X1–X11 supplies a special exception for them.

Keep those inherited provider failures visible. REPORT identifies them as three extra provider declarations, outside the 509 consumer-key union. Do not commission them implicitly or make them a reason to stop unrelated authorized consumer work. Actual edits to them require an explicit role/scope exception if the maintainer wants that additional work; this review grants none.

## Major API-01 persists in the immutable partial snapshot

The whole-NUPPT `ofPolyTimeUniform_def` alias remains at PPT:404, with exactly the same three uses at HardCore:266, HardCoreLemmas:1023 and HardCoreCollection:176. Existing `output_ofPolyTimeUniform` remains available. The previously reviewed substitutions and removal of the now-unused new alias remain appropriate without a public/data change.

All three old reader pairs still occur uniquely. The **complete old patch context** no longer matches HardCore (the adjacent negligibility reader changed) or HardCoreLemmas (the adjacent uniformity reader changed); HardCoreCollection's old hunk still matches. Thus rebase the tiny substitutions on current context instead of overwriting either new repair. The owner alias block/doc remains byte-identical to CP1. Exact current-source and mechanical-result hashes are in `validation.json`. This review did not apply anything. Root separately reports applying the four-file repair to its materialized review branch; that later checkout is not the immutable source reviewed here and no native result is attested here.

## Verification limits

Own `python3 -I validate_frontiers.py` passed 20 source/data checks: report/patch-head identity, role permissions, exact inherited provider proofs, API-01 persistence/context compatibility, proposal pins/header/acyclicity and 64 unary-length sanity cases including zero. Exact contract, relevant evidence and 17 inspected-source hashes are recorded. These checks are source/data verification, not Lean proof checking.

No incoming program was imported or executed; no Lean/native/cache/build/app command, source edit or Git mutation occurred. Only this ignored review/proposal directory was written. No final/merge/gate ruling, full-source review, complete frontier-impossibility proof or independent validation of all reported native/seal/census/control results is claimed. The delivered J/N work remains explicitly partial.
