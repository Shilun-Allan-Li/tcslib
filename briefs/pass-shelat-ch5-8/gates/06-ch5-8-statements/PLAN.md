# Gate 06: four external statement audits of ch. 5–8 (S4; internal draft)

**Status: internal reconciliation draft (2026-11-07); not issued or staged.** The source
reference reviewed here is `e9d64158461bfe24ddc88ab885bc4017899b4c16` on the local integration
branch. This is a review reference, not a final audit pin or a readiness attestation.

The user's 2026-11-04 gating ruling supersedes the original single-gate proposal: S2a and S2b
have API gates, and **each prong has its own statement gate before that prong's fills**. Gate
06A–D use one reconciled integration source and may be audited in parallel after the common
preparation below. No A → B → C → D audit order was imposed.

- **What is audited:** definitions, statements, docstrings and proof sketches against [PS10]
  and the second sources cited per item. Proofs are out of scope except the short proofs that
  carry a definition's correctness (including the protocol phase/correctness lemmas).
- **The tree:** S2b/#195 and the repaired ch. 2–4 API are merged; all four prongs and the
  repaired PAC/main transfer are incorporated. The current source includes the integration
  repairs below, public reading interfaces, four topic facades and their root exports.
- **Every pack carries:** relevant S2a/S2b APIs as context; the inventory and errata; the decision
  log and applicable rulings; `policy.md`; the exact source bundle/manifest; and primary-source
  access information in `source-manifest.md`. Goldreich drafts are linked for personal retrieval
  rather than redistributed. The author-hosted PSV copies have distinct recorded hashes from
  the historical publisher uploads; no byte identity is asserted.
- **Delivery:** the recorded external-auditor choice is Codex, with findings Markdown returned
  in chat. The user dispatches the jobs; the maintainer intakes and records the findings.

## Packs

Paths below are under `TCSlib/Cryptography/` unless qualified. Historical prong heads are
provenance only; none is the source pin for these integrated audits.

| Pack | Content | Integrated files | Items |
|---|---|---|---|
| 06A | Authentication, ch. 5 | `Authentication/{Defs,PRFMAC,Lamport,DLHash,HashAndSign}` and facade | Defs 134.1, 134.2, 135.1, 136.2, 136.a, 140.1; Protocols 134.3, 137.1, 142.2, 144.2; Theorems 135.4, 137.2, 142.3, 144.1 |
| 06B | Secure computation, §6.2 | `SecureComputation/{Defs,ObliviousTransfer,SpecialEncryption,SpecialEncryptionSecurity,Garbling,GarblingSpecial,GarblingSecurity,Hybrid,Compose,ComposePhases,ComposeSecurity,Yao,YaoReal}` and facade | Def 155.1; Alg 157.2, Claim 157.a; Constr 158.a, Claim 159.a; Def 160.a, Prot 160.4, Prop 161.5; Prot 162.6, Thm 163.7; the hybrid composition statement |
| 06C | Composability, ch. 7 | `Composability/{Defs,PRFScheme,CCA2Scheme,PublicKey,NonMalleable,SimNonMalleable,SequentialZK,ThreeColoring}` and facade | Defs 168.1, 171.5, 172.6, 173.7; Thm 168.2, Claim 169.a, Alg 169.3, Thm 170.4, Claim 172.a, Thm 174.8, optional Thm 175.9, Thm 175.1; the explicit sequential 3COL corollary |
| 06D | Randomness, ch. 8 | `Randomness/{Extraction,Learning,BPPBridge,Derandomization}` and facade; `LearningTheory/PAC/{Defs,Prediction}`, `InformationTheory/Samples` and their dependencies as already-gated context | Def 179.a; Thms 179.1, 180.1, 183.6 |

## Statement-phase findings retained for the auditor

- Algorithm 99.1's `Dec` refuses malformed ciphertexts (#193); its omission made the CCA1 claim
  false. The repaired guard remains in the shared base.
- `π′`'s tag covers `(r,c₁)`, not only `c₁` (the inventory erratum).
- Public-key games use canonical ciphertext padding and refuse non-canonical strings.
- Non-malleability follows [PSV06] and [PSV07]: CPA equivalence, and SIM ⇒ IND for every attack.
  The two maintainer sketches remain audit subjects; [PSV07] defers their proofs.
- `CRH` carries domain/range membership tests; Thm 144.1 retains its full-domain hypothesis.
- Thm 175.1 retains `Protocol.ProverBounded`; D8 alone does not bound honest prover messages.
- OT has five messages under D8. `SamplerCanonical` is now a theorem from the collection
  contract, not a security hypothesis. The canonical-encoding equation `henc`, polynomial-time
  evaluator hypothesis `hH`, and `EnhancedHardCore` remain explicit.
- Yao is audited first as an OT-hybrid protocol, with its real form a corollary of the separate
  honest-but-curious composition statement ([Gol04, §7.3], Q-5).

## Integration changes present in the reviewed source

1. **Canonical OT.** `SamplerCanonical` is derived by `Collection.sample_eq_encD`. The local
   decoding specification used by correctness follows from the retained canonical-only `henc`
   through `Collection.apply_of_decD`; callers no longer supply the old decoder-wide `hspec`.
   `hH : PolyTimeComputable H` and `EnhancedHardCore` are retained in OT and the real Yao theorem.
   Enhanced security still exposes the receiver's sampler coins to the predictor; it was not
   replaced by ordinary hard-core security. Def 155.1 includes efficient parties and bounded
   honest messages.
2. **Sequential ZK and 3COL.** The duplicate `ProverBounded` is deleted; the canonical definition
   is in `ZeroKnowledge/Interaction.lean`. `PerfectZK.seqRep` follows from `StatZK.seqRep` at zero
   error through `perfectZK_iff`. `PerfectZKAbort.seqRep` uses `PerfectZKAbort.statZK` and has
   statistical error `Q(n)·2^{-n}`; it does not claim exact perfect ZK. References use `[Gol01]`.
   `Composability/ThreeColoring.lean` adds `negligible_colSeqSound` and
   `colSeq_efficientProverProof_zk` at `Q(N)=2(N+1)^2`, with the explicit scheduling/count
   deviations. The corollary depends on the still-admitted generic repetition statements.
3. **PAC/main transfer.** Gate 05 closed, #194 reached `main`, and the repaired PAC layer is in
   the integration source. `PACLearnable` stays removed. `FinDist.probTrue` is now in
   `InformationTheory/FinDist.lean`, with its reading equation; Samples and PAC depend on that
   upstream home. The weak-learning confidence/amplification qualifications remain in force.
4. **Interfaces and exports.** Ordinary/predicate readers and explicit structure-field equations
   were added beside the prong definitions; machines are read through run/coin contracts.
   Public owner-side readers needed by the integration were added to base modules. The four
   topic facades and `TCSlib.lean` expose the new modules. T1/T2 sketches cite the extended
   public efficiency interfaces rather than claiming that the older statements suffice.
5. **DL-6/DL-7.** One `TCSlib.Cryptography.coinBlock`, its equation and length lemma live in
   `Asymptotic/Adversary.lean`; BlockEncryptor, Lamport, sequential ZK and both GI layers use it.
   Lamport's duplicate padding theorem is deleted. Lamport and CCA2 use
   `Collection.ofFn_padFin_of_le` from `Asymptotic/CollectionsHelpers.lean`, simplifying the
   zero-length padding suffix in the equal-length case. Ledger draft rows record local
   implementation, with final verification/landing still pending.

## Exact preparation and audit order

1. **Use the closed prerequisite gates and merged interfaces.** S2a/S2b and the repaired ch. 2–4
   interfaces are context, not fresh external audits here. For 06D, Gate 05's closing findings,
   repairs and the `main` transfer are also context. These integrations are present; the old
   holds for #195, Q-5, the honest-party efficiency ruling and #194 are stale.
2. **Finish common source verification.** Complete Rule-10 collection/seals over elaborated
   types and proof terms, including generated/private declarations and anonymous commands;
   retain sensitivity controls and an explicit-unfold scan including continuation lists.
   Classify inherited failures against the actual PR base; do not turn them into a blanket
   exclusion. Resolve actual touched-source failures, then replay every affected module and
   downstream module and reconcile final source/object fingerprints.
3. **Complete final attestations and attachment reconciliation.** Reconcile the `sorry` census,
   axiom records, declarations, style/API checks and recorded exceptions at the same final
   source. Use the verified primary-source URLs/hashes and version limits; do not redistribute the
   Goldreich drafts. Then select the full final source commit
   and records commit, build matching bundles/manifests and finish the four packs/prompts.
   This step has not been done by this internal draft.
4. **User dispatches 06A–D.** The four audits may run in parallel after steps 1–3. Each returns
   its named findings file; repair findings and repeat the relevant audit until it closes at
   0 blockers and 0 majors.
5. **Fills follow their own prong's statement gate.** Preserve the user's per-prong rule.
   The separate external S2 candidate-host fill is not silently included or accepted by this
   integration reconciliation, and its priority before clean-up part 2 remains unchanged.

## Evidence limits at this draft

The initial union and API replays spanned staged source versions. The later 158-module reader
and 25-module graph-sampler passes completed; `evidence-run/seal-ready-pinned.json` now
reconciles all 467 module source/object hashes and direct TCSlib prerequisite freshness at
the reviewed source. The root export file is outside this union and is verified import-only.
This is a reconciliation of serial checks, not a second cold build. Whole-file Rule-10 seals,
controls and final axiom dispositions remain pending. Source changes required by those checks
must receive a new affected replay and reconciliation before the audit pin is frozen.
No external gate is issued by this document.

**Not yet clear to merge — final seals/controls, source access reconciliation and gate dispatch remain.**
