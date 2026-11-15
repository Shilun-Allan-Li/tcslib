# Read-only checkpoint3 source audit

Revision: `04c253e48d9c0ebb73943f39412365cd4d8e02db`.
Issue base: `107f1e8c218733eac12d6b9bee6fece441271317`.
Auditor: seq-zk-a. Scope: all30changed/new Lean files, read from exact committed bytes.
No Lean command or source edit was used to reach these audit findings. A separately
authorized comment-only follow-up for StatisticalPrefix is recorded below.

## Result

No new public declaration is missing its docstring. All16new public definitions have a
literal `_eq` reader or the required `simps` field equations. No new public abbreviation
without an `_eq`/`_iff` reader was found. All39new proof bodies of at least15textual lines
have a `**Proof sketch.**` paragraph. Every changed target proof is shorter than15body
lines and retains its original or updated English sketch. Four target standard-axiom
checks are the lead's evidence, not a result rerun by this source audit.

The concrete source gaps are the absence of internal major-stage comments in the seven
new multi-stage proofs below. The policy does not give a numerical cutoff for “long”, so
the ≥25line cutoff here is an audit convention, not a claimed repository rule. The
47line StatisticalPrefix proof and the31–35line construction/endpoint proofs plainly
benefit from comments connecting their major steps to their existing sketches.

| Exact CP3 source location | Declaration | Proof body lines | Existing step comments |
|---|---|---:|---:|
| `TCSlib/Cryptography/Composability/SequentialZK.lean:462` | `seqVerifier_exec_first` | 28 | 0 |
| `TCSlib/Cryptography/Composability/SequentialZK.lean:563` | `seqRep_complete` | 35 | 0 |
| `TCSlib/Cryptography/Composability/SequentialZK.lean:609` | `seqRep_reject_of_first` | 33 | 0 |
| `TCSlib/Cryptography/Composability/SequentialZK.lean:714` | `seqRep_verifierSpec` | 30 | 0 |
| `TCSlib/Cryptography/Composability/SequentialZK.lean:756` | `seqRep_proverSpec` | 29 | 0 |
| `TCSlib/Cryptography/Composability/SequentialZK/SimulatorMachine.lean:310` | `exists_phaseSimulator` | 31 | 0 |
| `TCSlib/Cryptography/Composability/SequentialZK/StatisticalPrefix.lean:56` | `statClose_step` | 47 | 0 |

The lead acknowledged these exact seven findings and assigned comment-only fixes: five
owned SequentialZK bridges to the lead, exists_phaseSimulator to seq-zk-b, and statClose_step
to seq-zk-a. The seq-zk-a follow-up adds only three accurate major-stage comments, keeps
all tactics/types/APIs unchanged, and receives one native check under the normal own
slot/tag/tree. Its source and log have new evidence paths, preserving every CP3 receipt
snapshot byte. The other owners' dispositions remain in the lead's record.

## New definition/readers inventory

| CP3 source | Definition | Published reader |
|---|---|---|
| `TCSlib/Cryptography/Composability/SequentialZK/EndpointSampling.lean:43` | `coinTableEquiv` | `coinTableEquiv_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/EndpointSampling.lean:64` | `coinBlocksEquiv` | `coinBlocksEquiv_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/EndpointSampling.lean:148` | `realCoinsEquiv` | `realCoinsEquiv_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/Normalization.lean:49` | `normalizeMsgs` | `normalizeMsgs_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/PhaseView.lean:50` | `phaseViewPayload` | `phaseViewPayload_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/PhaseView.lean:66` | `normalizePhaseMsgs` | `normalizePhaseMsgs_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/Phases.lean:40` | `prefixProver` | `simps (config := { isSimp := false }) coins next` |
| `TCSlib/Cryptography/Composability/SequentialZK/PrefixFolds.lean:45` | `realStep` | `realStep_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/PrefixFolds.lean:64` | `simStep` | `simStep_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/PrefixFolds.lean:79` | `realPrefix` | `realPrefix_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/PrefixFolds.lean:92` | `simPrefix` | `simPrefix_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/SimulatorMachine.lean:54` | `phasePrefix` | `phasePrefix_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/SuffixMachine.lean:48` | `phaseStep` | `phaseStep_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/SuffixMachine.lean:154` | `phaseSuffix` | `phaseSuffix_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/WrappedVerifier.lean:48` | `phaseAux` | `phaseAux_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/WrappedVerifier.lean:93` | `phaseVerifier` | `phaseVerifier_eq` |

`prefixProver` is a structure-valued Strategy and uses explicit non-simp `coins`/`next`
projection equations. The equivalence-valued coin-table definitions have full literal
`_eq` readers, in addition to their useful block/tape readers. The two prefix folds and
suffix sequence likewise expose their complete equations. New specification structures
PaddedVerifierSpec and PaddedProverSpec publish their documented field projections.

## Rule10 source review

No new concrete explicit foreign-definition unfolding was found. The named `dsimp only`
lists in the helper modules refer to local lets (F,G,phase,index,K,act,count,upd,X,Z,RV,RS,
p,aux,raw), not imported definitions. Other naked `dsimp only` steps reduce local lets,
core products or core function application; they do not name a foreign TCSlib definition.
Published `_eq`, field, activation and execution readers are used for foreign constructions.
No new `unfold`, `delta`, generated `.eq_N`/`.eq_def`/`.eq_unfold` bypass, or global simp
attribute was found in the newly added material. Existing same-file definition reductions
in the owned original construction are not foreign-definition uses.

This is a static source audit. It does not certify all implicit definitional equality or
typeclass elaboration under irreducibility; the lead's complete A/B strict/coe seals and
explicit-scan evidence remain necessary. No native Rule10 check was run by this audit.

## Inherited original material, separately classified

ZeroKnowledge/Defs.lean is changed only by the approved nine-line StatZK_iff reader. The
original retry_poly at currentCP3line421 has a17line proof and an explanatory docstring
but no literal `**Proof sketch.**` paragraph. That proof/docstring is unchanged from the
issue base and is not a new fill regression. HVZK at137 and PerfectZKAbort at225 lack
literal same-name `_iff` readers in that frozen original file. PerfectZK at205 does have
the public lowercase `perfectZK_iff` at209; the case difference is not missing semantic
coverage. None of these original declarations is edited or requested for scope expansion.

The remaining admitted computational ZK.seqRep at CP3line832 and its numbered English
sketch are inherited unchanged at this checkpoint. Its completion is the lead's active
final work, not a newly introduced documentation omission.

## Method and retained evidence

cp3-source-audit.py reads each changed Lean file with git show at the exact revision,
compares declared names with the issue base, and records source SHA256, declaration/doc
locations, complete docstrings and textual proof lengths. The inventory contains220
textual declarations:158new (152public non-instance,6private). It treats declaration-level
comments/namespaces as proof boundaries; reported line counts are for audit triage rather
than a Lean parser claim. Every ≥15line candidate was reviewed against its nearby sketch.
The sixteen public-def reader matches and the seven commentless long proofs were also
checked manually against their committed source.

Retained new files: cp3-source-audit-inventory.json, cp3-source-audit-inventory.log,
cp3-source-audit-inventory.stderr, cp3-source-audit-docstrings.log, and
cp3-rule10-source-scan.log. These files were created after the closed181-file CP3 receipt
and are outside that historical receipt. No frozen CP3 source snapshot was updated.
