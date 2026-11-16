# Pass–shelat Gate 39 — seq-zk

**Verdict: HOLD. Counts: 0 blockers, 1 major, 0 minors, 0 notes.**

No mathematical defect was found in the five target proofs. An undisclosed inline
re-proof of an earlier public helper remains. The issued duplication rule makes this
major even though it does not invalidate the mathematics.

| Item | Audited revision |
|---|---|
| [Draft PR #327](https://github.com/Shilun-Allan-Li/tcslib/pull/327) | `bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa` |
| Exchange | `da8f8f66e505a9e27034667ff68a3b104036e84e` |
| Campaign records | `d5a3e2d0c399b918d72e5a51732905625e500bd2` |
| PR base | `05d26fe5b41fcb9426ec220d877d03264b9c8e8c` |
| Issue base | `107f1e8c218733eac12d6b9bee6fece441271317` |

This is a source audit and an independent recheck of supplied native evidence, **not a
fresh Lean build**. The live PR metadata confirmed the requested head. No repository
source, PR, dispatch record, or merge was changed.

## Finding

Paths in this section are under `TCSlib/Cryptography/Composability/SequentialZK/`.

| ID | Severity | File · declaration | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| G39-01 | **major** | `RealPrefixBounds.lean:83` · local `hsource` in `PaddedProverSpec.realPrefix_bounds` | Re-proves the public `PaddedProverSpec.next_length_le` from `ProofTransfers.lean:38`, specialized to `r := tape`. The public lemma arrived in landing commit `29b81e8ba`; the inline re-proof arrived later in `5fa0430ca`. The REPORT describes both helpers but does not disclose this overlap. Its account of `realPrefix_bounds` cites the specification reply readers and ExecutionBounds, omitting the exact existing public helper. | Import `SequentialZK.ProofTransfers` and derive `hsource` directly from `d.next_length_le y B hbound tape hist`. Preserve headers, correct the overlap record, and refresh affected checks. |

The existing public conclusion is:

```lean
(hB : ∀ r hist, (π.P.next x y r hist).length ≤ B) :
  ∀ r hist, (ρ.P.next x y r hist).length ≤ B
```

The later local proof is:

```lean
have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B := by
  rw [d.next y tape hist]
  dsimp only
  split_ifs <;> first | exact hbound _ _ | exact Nat.zero_le B
```

This is the same bound and branch argument. The replacement uses the public lemma:

```lean
have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B :=
  d.next_length_le y B hbound tape hist
```

The proposed import is acyclic: the existing `ProofTransfers` closure does not contain
`RealPrefixBounds`. This replacement is a proposed repair, not a newly compiled patch.
The complete final REPORT and the supplied checkpoint REPORTs do not identify this
particular re-proof; the reported overlap between `next_length_le` and the owned
`ProverBounded.seqRep` is a different relation. This finding concerns an earlier helper
within this PR, not a lemma predating the issue base. The brief explicitly includes
duplication inside parts of proofs. A scan of top-level statements cannot detect this
local `have`.

The evidence ZIP contains the compared fragments, their commit provenance, the relevant
REPORT passages, and the import-closure check. The gate remains HOLD until G39-01 is resolved.

## Proof assessment

The author-hosted [PS10 notes](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf),
Theorem 175.1, pp. 175–176, and
[Goldreich's chapter draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part4N.pdf),
§4.3.4, Lemma 4.3.9, support the wrapped-verifier and sequential-simulation route. The
fixed move budget, even padding, bounded honest-prover messages, and strict-PPT simulator
convention are explicit adaptations of the frozen interface.

1. **Normalization and simulator.** `PhaseView` validates the known common input,
   auxiliary input, empty wrapper tape, and canonical encoding. It normalizes to the
   prescribed bounded real-message slots and uses empty slots on malformed outputs.
   `normalizePhaseMsgs_viewV` proves the real-view fixed point. The simulator therefore
   needs no hypothesis about the shape of simulated outputs. `SimulatorMachine` realizes
   the recursion through the existing counted-loop host; its orbit-size bound is
   polynomial on every tape.

2. **Uniformity and quantifier order.** `exists_phaseSimulator` constructs `SQ` using
   `NUPPT.ofPolyTimeUniform` and explicitly proves `SQ.Uniform`. Its coin polynomial is
   `V.coins + Q*S.coins`: one verifier tape and independent simulator blocks. Both transfer
   theorems choose `S` and `SQ` before any auxiliary-input bound or distinguisher. The
   nonuniform metadata is used only in `exists_phaseReduction`, not in `SQ`.

3. **Computational ZK.** The encoded-prefix envelope is
   `Q(n)*π.rounds.eval n*(2*B(n)+2)`. `ComputationalPhaseBound` uses the larger polynomial
   `2*n + 2*Lz(n) + 2*V.coinLen n + 2*Q(n) + envelope + 8` for packed metadata and hence for
   the wrapped auxiliary input. Finite metadata covers all bounded prefixes. The selector
   maximizes witness-indexed suprema before the negligible bound is requested, so no
   witness-length bound or attained witness maximum is assumed. The reduction stores no
   witness and performs no reachability or witness-validity test. The continuation drift
   and endpoint readers give advantage at most `Q(n)*|ε(n)|`; the existing
   `Negligible.polyExpr_mul` proves negligibility. `ZK.seqRep` instantiates this result
   without changing its hypotheses.

4. **Statistical ZK.** A raw one-phase comparison is mapped through the same normalizer
   and padded-prefix update. Averaging, randomized postprocessing, and the triangle
   inequality give **exactly `Q(n)*δ(n)`**. The real and simulator endpoint equivalences
   add no error. Nonnegativity of `δ(n)` is obtained from the one-phase comparison on a
   witnessed input. `StatZK.seqRep` directly instantiates the padded-prover theorem.

5. **Interactive-proof cases.** Completeness transfers phase by phase, using exact coin
   slices and the all-phase verdict. `InteractiveProof.seqRep` preserves its original
   negligible rejection bound through phase zero. For explicit error, the fixed-prefix
   prover and verifier-prefix independence show that each fresh phase accepts with
   probability at most `s(n)`, after any earlier prefix. The adaptive product theorem
   gives **`s(n)^Q(n)`**, without assuming independence of the adaptive success events.
   `sound_nonneg` supplies the sign needed for multiplication. The efficient-prover case
   additionally supplies the repeated prover's uniform efficiency, message bound, and
   completeness for every valid witness. The unused `hQ` in the explicit-error theorem
   is already disclosed.

6. **Boundary cases.** The recursion and endpoint equations include zero phases for ZK
   and statistical ZK, with empty history and zero accumulated error. The explicit-error
   engine permits zero phases with bound one; the frozen proof-system statements retain
   their positive-phase hypothesis. Zero rounds, either first mover, and odd round counts
   are covered by the padded phase contracts. Honest prover fillers are empty; cheating
   verifier filler messages are not restricted. The delivered sketches describe this
   route. Only the statistical target's sketch changed from the issue base.

## Integrity, scope, and native evidence

| Check | Result |
|---|---|
| Pack integrity | All **24** outer manifest entries verify. Verification: **147** entries; nested review evidence: **1106**; LE-doc: **58**; integration: **1248**. Each extracted ZIP file set equals its manifest plus `SHA256SUMS`. The 25 pack files, including the manifest, match pinned exchange Git blobs. |
| Source provenance | All **185** source-closure files match the head's Git blobs. The complete **1319-file Lean tree** at the head was also checked against Git blobs for duplication searches. All 41 changed-file inventory hashes agree. The diff reproduces: **41 paths, +6652/−14**. |
| Frozen statements | Replayed declaration comparison gives **196 ADDED, 0 CHANGED, 0 REMOVED**. All **27 + 35** pre-existing declaration headers, their order, definition bodies, and statement prose are preserved. The frozen scanner returns **0 differences**. The two pre-existing files are also unchanged between the issue base and PR base. |
| S-01 | `StatZK_iff` is precisely the existing predicate's simulator property by `Iff.rfl`, with no attribute. The approved code matches apart from blank-line placement; LE-doc supplies its formula. No other pre-existing `Defs` declaration changes. |
| LE-doc | **23 files, 81 changed docstrings**; deleting doc comments leaves byte-identical code. All inserted formulas agree with their declarations/readers or the documented handwritten structure/recursion descriptions. No target docstring changes in LE-doc. |
| Build records | Independently checked hashes and recounted both diagnostic forms in **303 review build logs** and **715 integration records**, representing **694 effective modules**. All effective results have rc 0 and zero errors. All **694 effective source hashes** match the disjoint published PR changes over the pinned records commit; all **41 unit source hashes** equal the audited head. This comparison does not depend on fetching the maintainer's unpublished scratch tree. |
| Rule 10 | Rechecked **154 head probes and 8 base probes**: raw log hashes, executed probe hashes, removal of instrumentation back to the exact source revision, and install/EOF masks. The **10 omitted coe probes** are byte-identical to their executed strict counterparts, accounting for all **164 effective head cells**. |
| Rule-10 failures | Only `Defs` fails: **10 errors in each variant at both base and head**, in the same six unchanged declarations: `perfectZK_zeroRounds`, `AbortRetry.attempt_poly`, `AbortRetry.exists_retrySimulator`, `AbortRetry.statClose_retry`, `PerfectZKAbort.statZK`, and `negligible_inv_pow_sqrt_div`. **New failing declarations: 0.** `StatZK_iff` passes. |
| Controls and explicit reads | Recounted all **24** strict/coe control logs. The supplied paired-control interpretations and explicit-read attribution agree with the inspected readers and proof bodies. Coe-A remains canonical. No additional Rule-10 violation was found. |
| Axioms and admissions | Parsed all **414** stored-constant census rows: the axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. The five targets and reported consumers print only standard axioms. The supplied admission census changes **23 → 18**, removing exactly the five targets. |
| Ownership and sweep | The ownership table assigns each of the **39 helpers** one owner: lead 5, a 10, b 9, c 15. The supplied lead-tagged, same-module slot records cover the **276** final-sweep checks; the recorded maximum is three slots. This establishes consistency of the provenance records, not independent authentication of who operated the host. |
| Style and API | Largest file: **992 lines**; maximum width: **100**. No new global simp attribute. The Prop-valued `Nonempty` instance is disclosed. Public definitions have readers; the long proofs have sketches. The supplied lint line-set comparison introduces no new failure. |

The combined integration build is accepted as evidence for the final merged state, as
dispatched. Merge order, **#324 last**, and any maintainer rebuild for the second merge
remain merge conditions and are not audit findings.

## Documentation and duplication disposition

The **11 truncated formulas** were assessed individually under G37-03. They are not
automatic failures: their own accompanying prose states the omitted property.

| File | Declarations | Assessment |
|---|---|---|
| `ComputationalHybrid` | `prefix_distAdv_joint_le`, `distAdv_view_endpoints` | The prose states the joint `Q(n)*ε` bound and the exact advantage identity between actual and typed endpoints. |
| `ComputationalReduction` | `reductionData_fields`, `exists_continuationSampler`, `exists_phaseReduction` | The prose supplies all five fields, the sampler's activation equation, and the continued distinguisher computation with its separate coin portions. |
| `ContinuationProbability` | `continuationProb`, `continuationProb_eq`, `continuationProb_real`, `phaseGap`, `phaseGap_eq` | The prose identifies acceptance of the remaining canonical suffix under the full typed table, its real-step expectation identity, and the raw real/simulator gap through the randomized continuation. These descriptions state properties rather than merely referring to a definition. |
| `EndpointSampling` | `simulate_eq_simPrefix` | The prose states the raw split-tape to typed-prefix output identity. |

The strict-PPT note is accurate and visible in the module's deviations and in
`PerfectZKAbort.seqRep`. PS10's sequential-composition sketch explicitly discusses expected
running time. Goldreich's Definition 4.3.1 uses a strict polynomial-time simulator with
abort and the exact conditional law. The code starts from that strict aborting premise
and uses bounded independent retries; it does not claim a general conversion from
expected-time perfect simulation preserving an exact conditional law.

The broader duplication search covered the hybrid arguments, statistical postprocessing,
coin-block readers, encodings, and history accesses. The code directly uses
`abs_sub_le_sum_hybrids`, the published `StatClose` laws, `FunFamily.blocks`, the existing
coin equivalences, `CommitmentLemmas.encodeMsgs_append`, and
`CommitmentLemmas.length_encodeMsgs_le`. The disclosed Yao encoding equality and repeated
block specializations are not reopened. A supplementary statement comparison, including
binder renaming, found no hits for the 175 new theorems against 20,640 other parsed
theorems. G39-01 was found by inspecting an inline proof, outside that scan's coverage.
No other undisclosed duplication was identified; these searches are not a decision
procedure for semantic equivalence.

**Notation (source notation):** `π`, `ρ`: original and repeated protocols; `R`: witness
relation; `n = |x|`; `Q`, `B`, `Lz`: phase, message, and auxiliary-input bound polynomials;
`S`, `SQ`: phase and repeated simulators; `δ`, `s`: statistical and soundness errors;
`ε`: negligible comparison bound.
