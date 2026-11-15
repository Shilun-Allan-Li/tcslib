# Pass–shelat Gate 32 — headD promotion

**Verdict: HOLD.** The promotion, preserved API, placement, documentation, and supplied seal evidence pass inspection. The required duplication inventory misses further copies outside DL-47. Under pack question 3, these require a repair or an explicit additional debt disposition before this gate closes.

| Blocker | Major | Minor | Note |
|---:|---:|---:|---:|
| 0 | 1 | 0 | 0 |

One major groups the undisposed occurrences of the same reader identity.

| Pin | Audited revision |
|---|---|
| PR | [Shilun-Allan-Li/tcslib #316](https://github.com/Shilun-Allan-Li/tcslib/pull/316), draft |
| Lean head | `c18afbe66101381eed1617801d942dcf691506ea` |
| Parent / comparison base | `dd98360d4886ac68fab34899b8bd0d12ae9a0aef` |
| Campaign records | `3433097294600c7cd1ce30f5a5cc005c4ff0e4a4` |
| Exchange | `22df0b71465fd1148fdd94dc4751a43d41614162` |
| #313 consumer inspected | `94b31964ee94b97bf3ed3b4b4338cacae8183194` |
| #315 consumer inspected | `fbd37f447596d4207c8d08b7ef7602f57fe95198` |

## Finding

Paths in the findings are relative to the repository root; line numbers refer to the audited Lean head.

| ID | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G32-01 | major | `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450`, local `hbit` in `step_eq`; further occurrences below | DL-47 is incomplete: additional proofs independently compute the head or defaulted entry of `List.ofFn`, including an exact copy of the entire promoted statement. | The `hbit` statement is exactly `headD_drop_ofFn x ⟨d.i, hi⟩ false`. It is proved again with `List.drop_eq_getElem_cons`, `List.headD_cons`, and `List.getElem_ofFn`. DL-47 identifies neither this occurrence nor the additional scalar reductions listed below. | Re-point the scalar readings through the promoted theorem and a shared getD reader derived from it, preserving existing headers; alternatively obtain an explicit disposition for the additional occurrences and record their locations and cleanup plan. |

The decisive exact copy is:

```lean
  have hbit : ((List.ofFn x).drop d.i).headD false = x ⟨d.i, hi⟩ := by
    rw [List.drop_eq_getElem_cons (by simpa using hi), List.headD_cons, List.getElem_ofFn]
```

Its replacement term is precisely:

```lean
    TCSlib.Cryptography.headD_drop_ofFn x ⟨d.i, hi⟩ false
```

A separate, equally direct getD occurrence is `TCSlib/Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69`:

```lean
    have : (fun i : Fin n => (List.ofFn a).getD i false) = a := by
      funext i; simp [List.getD_eq_getElem?_getD]
```

After `funext`, this is the in-range getD form that pack question 3 expressly includes. That form follows from the promoted theorem and `headD_drop`; the proof above instead computes it again.

The following additional locations were inspected in context. Each relevant file has the **same Git blob at the parent, audited head, and records pin**. They are pre-existing residuals within the gate's expressly requested scan. The finding does not include any occurrence already listed in DL-47, the retained Lamport alias, or #313's separately scheduled `firstBit_of_pos` edit.

| Source location | Declaration / step | Unlisted reader computation |
|---|---|---|
| `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean:449–450` | `step_eq`, local `hbit` | Exact headD/drop/ofFn statement above. |
| `TCSlib/Cryptography/Asymptotic/HardCoreLoops.lean:278–280` | `orbit_eq`, successor case | The same headD/drop/ofFn computation for `β`, using a dropped-list constructor and `headD_cons`. |
| `TCSlib/Cryptography/SecureComputation/Garbling.lean:193–198` | private `map_range_getD_ofFn` | After list extensionality, computes `(List.ofFn ass).getD i false` by converting to indexed access. |
| `TCSlib/Cryptography/SecureComputation/Garbling.lean:375–380` | `garbledValues_getD`, input case | Computes the in-range entries of `inputKeys` and `List.ofFn x` through `getD_eq_getElem` and simplification. |
| `TCSlib/Cryptography/SecureComputation/Yao.lean:626–627` | `yaoBobTables_yaoMsg` | Inline getD/ofFn computation through `getD_eq_getElem` and `getElem_ofFn`; separate from DL-47's private lemma at line 611. |
| `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean:107–113` | private `ofFn_half`, both branches | Remaining in-range getD/ofFn reductions after applying the published split-half readers. DL-33 names the older split-half overlap; it does not list these scalar reader residuals. |
| `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/PaddedCPA.lean:72–78` | private `ofFn_splitHalf_bit` | Both two-bit cases compute the selected getD/ofFn entry by expanding `List.ofFn_succ` and simplifying. |
| `TCSlib/Complexity/CircuitComplexity/CircuitEvalNP.lean:68–69` | `dagCktSatLang_mem_NP` | Function-extensional getD/ofFn identity quoted above. |
| `TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean:188–190` | `runWith_embedGates_getD` | Computes `(List.ofFn xD).getD v false` in the input relation. |
| `TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean:383–387` | `progGates_values`, input-source branch | Computes `(List.ofFn x).getD k false` through `getD_eq_getElem` and `getElem_ofFn`. |
| `TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean:127–132` | `snapEncode_injective` | Computes two getD/ofFn entries after applying the same coordinate to both encodings. |
| `TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean:427–431` | private `tabSrc_eval` | After removing the prefix, computes the in-range entry of `List.ofFn x`. |
| `TCSlib/Complexity/Randomized/RandomWalk.lean:256–259` | `decodeIdx_succ_append`, local `hu` | After reading the left append, computes `(List.ofFn u).getD j false`. |
| `TCSlib/Complexity/ClassPSPACE/TQBF.lean:857–859` | private `codecRow_realize`, local `hi` | Computes the getD/ofFn function identity with `x := List.ofFn r.input`. |
| `TCSlib/Cryptography/Encoding/BooleanVector.lean:168–171` | `expandPoly_encode`, local `hbit` | Computes the in-range optional entry of `List.ofFn (padFin …)`, then takes its defaulted value: the getD form in optional-access notation. |
| `TCSlib/Cryptography/Hashing/SIS/CollisionOutput.lean:237–243` | `collisionOutputPoly_pairEncode`, local `hbits` | The same defaulted optional-entry computation for each of the two `rawCollisionInputs` vectors. |

The exact GGM copy alone establishes G32-01, independently of judgments about the surrounding list equalities. The getD cleanup should have one generic reader, derived from `headD_drop` and the new theorem, so both Boolean and non-Boolean consumers can cite it.

## Checks that pass

| Area | Audit result |
|---|---|
| Pack integrity | All **14** outer manifest hashes, **61** verification-manifest hashes, and **476** nested-evidence manifest hashes pass. The verification ZIP contains exactly its manifest paths plus its manifest; the nested evidence has exactly 477 files, including its manifest. All **149** source-ZIP files match the pinned head. |
| Source identity and scope | Independently checked tree `68caf9d0f20e2ef9c51d2794dd5c248766337e50`, parent, exact two-path diff, and 1,339 pinned files under `TCSlib`, `audits`, and the root facade. The supplied diff equals the Git diff byte for byte. The pack, G29 resolutions, and DL-47 match the records pin. |
| Placement and imports | `BitLists` is an appropriate shared home. Its four imports are Mathlib modules; it has no project ancestor. `MachineSpec` imports it directly. Both files' imports are unchanged. No new cycle or undisclosed import is introduced. The graph has 244 descendants of `BitLists` and 5 of `MachineSpec`, excluding the modules themselves. |
| Frozen API | All **23** pre-existing headers are byte-identical: 14 in `BitLists`, 9 in `MachineSpec`. There is one added theorem. Lamport's proof is the fully qualified application of the shared theorem; its only documentation change is the disclosed paragraph. Retaining its public name implements the ruling. |
| Proof and documentation | The generic statement covers arbitrary `Type*`, default, and in-range `Fin` index. Its proof uses the stated published lemmas, with no new admission or definition unfolding. The formula, bit-vector remark, main-results bullet, and sketch are accurate. The glue-lemma source-tag exemption applies; the one-line proof would not require a sketch. |
| Name resolution | The sole unqualified use in `run_input` is inside `Authentication.LamportFill`, where the retained local theorem remains the nearest name. The new theorem has no attribute and adds no instance. No additional named use appears in the inspected #313/#315 changes. |
| Rule 10 | All eight supplied A/B strict/coe seal runs pass. Independently verified their source/probe hashes and recovered the exact audited source by removing only the recorded insertions. MachineSpec request counts are 2088/2089 strict and 2087/2088 coe. BitLists has zero requests in each variant, correctly disclosed as vacuous; its proof reads no foreign project definition. |
| Controls | Independently checked probe/log hashes and error locations against both control plans: four probes per harness; each of 15 sealed negatives fails exactly once, every paired reader passes, unsealed probes pass, and no stray error remains. |
| Build and axioms evidence | All 253 supplied build rows report rc 0 and zero errors in both forms; every source hash matches the head and every log hash verifies. The 24 admissions are disclosed baseline admissions. The supplied comparison reports 249 byte-identical same-source oleans. The axiom log reports `[propext]` for both readers and the standard three axioms for `run_input` and `lamport_oneTimeSecure`, without `sorryAx`. |
| Lint and dimensions | FAIL/WARN lines are identical: 92 FAIL / 101 WARN. The two files have 192 and 269 lines, maximum width 100. The comparison's `RESULT FAIL` concerns the intentionally changed Lamport docstring; its header comparison passes. |
| Other listed debt | DL-47 correctly identifies its listed occurrences and their tip locations. Its `BitLists:75` becomes line 88 at this head. Those listed copies remain outside the finding under the ruling. |
| #313 and #315 | All five #313 changed modules already reach `BitLists`; specialization at index zero supplies `firstBit_of_pos` after `firstBit_eq` and `List.drop_zero`, without a new import. That edit and Gate 29 round 2 remain separate. Five of six #315 changed modules reach `BitLists`; none adds another copy or touches either promotion file. |

## Merge condition and verification limits

The rebuild after combining #316 with the tip containing #314 remains the **maintainer's pending merge condition**, as dispatched. It was not treated as an audit item or a finding. No concrete conflicting name, instance, or import interaction was found. This audit does not claim to establish that integration build or the #313/#315 combined builds.

Verification here comprises independent Git/source, manifest, import-graph, probe-preservation, and diagnostic-log checks, plus manual proof inspection. **No Lean process was run by this auditor.** The kernel-build and axiom results above are attributed to the supplied, hash-checked evidence.

The companion ZIP contains this Markdown, the independent check scripts and results, numbered overlap excerpts, the relevant pinned sources, the pinned debt ledger, and hash verification details. No repository changes, dispatch, review submission, or merge was performed.
