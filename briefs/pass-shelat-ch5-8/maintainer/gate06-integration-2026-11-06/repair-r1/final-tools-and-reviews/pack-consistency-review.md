# Gate 06 pack consistency: internal read-only review

Reviewed 2026-11-07. Verdict: **issue after bounded record updates and completion of the already-required final checks**. This is a pack/source consistency review, not a statement audit or proof-pass attestation. No new external job was prepared; no Lean, cache, apps, delivered programs, library, campaign, evidence or Git mutation was performed. This file is the only new artifact.

Inputs are main-records `briefs/pass-shelat-ch5-8/gates/06-ch5-8-statements/`:

| File | SHA-256 |
|---|---|
| PLAN.md | `4c00fda9f3c8c8664255bbd4d2776bb54db654ce49c98087113a8b938aa9bb26` |
| 06A-pack.md | `414da001364cc0a98e9be921338ec933dcb649eedc9162029739d928872d175d` |
| 06B-pack.md | `89e01907f0bc37f30935b9d6e23697998705429e7a0524f7549466fd85aa2eaf` |
| 06C-pack.md | `e878101ad806d66bba1c94db0dc273467f7036c2ebaf25faf82fe6b704fc9945` |
| 06D-pack.md | `e33be6c592fe78a69e46bec8733fd1955a4f6b7ac0e0ed6e4c2b7b0fbf39ee3f` |
| source-manifest.md | `13fc6f5874ed1e4b251088a68a34893a65cd5a78e3eb138df02bafdc7812a57c` |

Observed integration checkout: `/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`, clean tracked status at `052b387a204f476e1dad1ca51bd256ec1bbef34f`. This observation is **not** selection of the final issued pin. Historical survey base/head are `c7d8753a548ced71c1e1ea70e012c365af5c2171` / `e9d64158461bfe24ddc88ab885bc4017899b4c16`.

## 1. Required issue-time replacement: shared revision and evidence prose

Sites: each pack lines 3–8; PLAN 111–119; A 79–87, B 100–110, C 122–132, D 76–84; also B 55–56, C 75–76, D 44–45. The earlier 467-record reconciliation is valid historical evidence at e9, not a current-source attestation after repairs. “Seals/controls pending” also obscures the completed failed initial survey. Do not merely substitute a new head into the old paragraph.

Use this common header **after final reconciliation**, filling every bracket from retained evidence:

> **Status: [prepared / dispatched, as actually applicable].** Source `[FINAL_SOURCE_HEAD]`, actual PR base `[ACTUAL_PR_BASE]`, records `[RECORDS_HEAD]`. Exact bundle/manifest: `[PATH, SHA256]`. Final preparation evidence: `[INDEX, SHA256]`, at the same source pin. It separately reports source/object/prerequisite freshness; dynamically scoped collection, full seals and controls; source failures and inherited dispositions; census/axioms; and source/style/API scans. Historical prong and e9 survey heads are provenance only. Auditor: Codex; findings Markdown in the audit chat; the user dispatches the job.

Replace PLAN's “Evidence limits at this draft” paragraph and the repeated 467-record bullets with:

> The e9 survey is retained historical evidence: all 51 harnesses had valid installation/EOF markers; 17 modules passed and 34 failed with 195 source diagnostics. Exact source classification identified 120 diagnostics in unchanged declarations and 75 in new/changed declarations. Subsequent ordinary checks and old-collector diagnostic seals are repair evidence, not final coverage. The issued source's native reconciliation, fresh dynamic collector/seals/controls, scans and axiom dispositions are recorded in `[FINAL_EVIDENCE_INDEX, SHA256]`. Report every remaining source failure and its actual-base disposition; unchanged inherited failures remain failed observations, not seal passes or exclusions. The root `TCSlib.lean` export source is included; state separately whether it was only checked as import-only or actually elaborated.

At issue the final index must supply the actual dynamic module list/count and results, not reuse 51, 54 or the old collector rows. In particular, the added owners `Asymptotic/MultiMessage.lean`, `Complexity/Randomized/PolyTimeModel.lean` and `ZeroKnowledge/Encoding.lean` must not disappear through a historical file list. Preserve all term/private/generated and anonymous-command coverage and approved notation treatment. No new approval gate is proposed.

## 2. Source and statement boundaries already consistent; retain them

- Worker route and order are already correct (PLAN 7–10, 23–24, 104–107; decision log rows 219 and 420): per-prong gates, all four may run in parallel after common preparation; Codex returns Markdown in chat. Do not reinstate Claude delivery/exchange pushes or an A→B→C→D chain.
- B 38–44 and 79–85 match current `ObliviousTransfer.lean` and `YaoReal.lean:107–120`: canonicity is derived, canonical `henc` is retained, and polynomial evaluator cost `hH`, OneWay and `EnhancedHardCore` remain explicit. There is no bare enhanced-hard-core route. Keep the five-message/output convention and HBC efficient-party/bounded-message rulings.
- C 61–72 match canonical `ProverBounded`, strict-PPT abort retries with statistical error `Q(n)·2^{-n}`, and `ThreeColoring.lean:106–132`: count `2(N+1)^2`, finite `N=0` prefix, filler scheduling rather than `colProtocolRep`, and admitted generic repetition inputs.
- C 102–114 match current `NonMalleable.lean:34–44` and `SimNonMalleable.lean:476–527`: PSV06 copies and invalid ciphertexts both become bottom; PSV07 distinguishes COPY. The one-challenge complementary-pair copy-flag sketch, including message length zero, is an audit subject, not an established many-challenge bridge. The two implication proofs remain admitted. Do not claim literal convention identity or a recovered full PSV proof.
- A's domain/full-group/full-domain-CRH qualifications and D's fixed uniform learner/confidence-gap/amplification qualifications agree with the bounded source inspection. Derived correctness/existence/PAC conclusions can depend on admitted security statements; “proved” in the tables does not mean all transitive axioms are standard.

Recommended one-sentence clarification after C's scope table (source fact, not new work):

> `CCA2Scheme.lean` constructs private-key encryption. `PublicKey.lean` defines public-key attack games and the conditional padded CPA bridge of Claim 172.a; no public-key CCA2 construction is claimed.

This agrees with the user's separate IND-CPA/IND-CCA2 implications endpoint ruling (decision-log rows 432 and 435); that ruling does not create a construction in Gate 06.

PLAN 108–109 may be refreshed without reopening S2:

> The S2 candidate-host fill retains its separate source pin and acceptance/landing record; Gate 06 does not attest it. Bundle only source bytes present at the chosen Gate 06 head. Clean-up part 2 still follows S2 merge under the standing order.

## 3. Source access: retain limits; two small stale action phrases

The recorded local PS10, PSV06/07 author and all three Goldreich file sizes/hashes were independently rehashed and match `source-manifest.md`. No PDF content or network access was re-audited here. These bytes establish identity of local copies, not availability in the receiving Codex session or publisher-version identity.

- A: PS10 §5.1–5.6, book 133–145. B: PS10 §6.2, book 154–164; linked Gol04 §7.3 and Appendix C.1 drafts. C: PS10 §7.1–7.2, book 167–176 plus 124–129; linked PSV06 Definition 3, PSV07 Definitions 1–4/Theorems 3–4/Corollary 1; linked Gol01 Definition 4.3.1/§4.3.4. D: PS10 §8.1–8.3, book 179–184. Preserve the PS10 PDF-to-book offset 12.
- Goldreich remains **link/access only**: no PDF, full text, rendered pages or book excerpt attachment. Draft numbering/pagination is not a verified published-edition mapping. The formal strict-PPT abort premise is not the expected-time formulation; Appendix C.1 defines enhanced inversion, while the Boolean predicate is motivated also by §7.3.2, not literally defined there.
- PSV author URLs/hashes stay labelled author copies, byte-distinct from historical publisher uploads; no blanket redistribution license or missing full-proof access is asserted.
- KV94/SSBD14 comparisons are previously gated context; Gar26 probability APIs are context. Do not claim fresh access or source verification for these. If the receiving auditor cannot access a cited source, report the exact unavailable comparison and do not give blanket source-fidelity approval. This is an access disclosure, not a request for a new mathematical ruling.

`source-manifest.md:95` can become: “The packs retain the following two citation-precision qualifications; preserve them in the issued source/bundle.” Lines 129–131 can become:

> The current 06B/06C drafts carry these citation qualifications. At issue preserve the author-version labels, COPY/invalid-output distinction and link-only Goldreich delivery, and record the receiving auditor's source-access basis or exact remaining limits.

## 4. Exact bundle path sets (not staged by this review)

Let `C = briefs/pass-shelat-ch5-8` and `G = C/gates/06-ch5-8-statements`. Common records: root `policy.md`, `PassShelatChapter5-8Plan.md`; `C/inventory-ch5-8.md`, `C/duplication-ledger.md`; `G/PLAN.md`, `G/source-manifest.md`, and the relevant `G/06X-pack.md`; the final evidence index and every artifact it cites for audit acceptance, with revision-qualified paths/hashes. Do not present old failed/unrun attempts as the final checks; retain their actual status in the index. D additionally carries `C/gates/05-pac/{findings/gate05-pac-r3-findings.md,resolutions-r3.md}` as closed-gate context.

Primary Lean subject sets below use `.lean` on every name; braces are set notation, not a shell command:

| Pack | Primary paths |
|---|---|
| A | `TCSlib/Cryptography/Authentication.lean`; `TCSlib/Cryptography/Authentication/{Defs,PRFMAC,Lamport,DLHash,HashAndSign}.lean` |
| B | `TCSlib/Cryptography/SecureComputation.lean`; `TCSlib/Cryptography/SecureComputation/{Defs,ObliviousTransfer,SpecialEncryption,SpecialEncryptionSecurity,Garbling,GarblingSpecial,GarblingSecurity,Hybrid,Compose,ComposePhases,ComposeSecurity,Yao,YaoReal}.lean` |
| C | `TCSlib/Cryptography/Composability.lean`; `TCSlib/Cryptography/Composability/{Defs,PRFScheme,CCA2Scheme,PublicKey,NonMalleable,SimNonMalleable,SequentialZK,ThreeColoring}.lean` |
| D | `TCSlib/Cryptography/Randomness.lean`; `TCSlib/Cryptography/Randomness/{Extraction,Learning,BPPBridge,Derandomization}.lean`; context `TCSlib/LearningTheory/PAC.lean`, `TCSlib/LearningTheory/PAC/{Defs,Prediction}.lean`, `TCSlib/InformationTheory/Samples.lean` |

For each pack include the **complete final-head TCSlib import closure** of its primary/context source set, derived from the final source inventory, and `TCSlib.lean` for root-export context. Relevant Games/Interaction/Machines/Collections/FinDist/complexity owners then arrive automatically; do not send only the historical prong tree or an e9 copy of a repaired dependency. Mark prerequisite and helper owners as context rather than silently adding another external statement audit. Every included path must have final-head raw bytes and manifest hash. Mathlib/toolchain/package versions belong in the environment manifest, not invented source-copy claims. PS10 source access uses its recorded campaign PDF; linked third-party sources use the access arrangement above.

## Issue-time checklist

- [ ] Freeze actual source/base/records and matching bundle hashes after root's final checks; retain any source mutation's affected/downstream replay.
- [ ] Replace all e9/467/current-manifest and generic pending-seal wording using the final dynamic evidence; qualify all inherited failures and invalid harnesses.
- [ ] Publish census/actual axiom identities/dispositions and source/style/API scan results at that same head, with precise exceptions.
- [ ] Carry all four primary/context path sets, complete source closures, source-access/version limits and COPY/strict-PPT/enhanced-predicate qualifications.
- [ ] Keep Codex/chat deliverables `gate06A-findings.md` … `gate06D-findings.md`, user dispatch, parallel-after-common-prep order, per-prong 0-blocker/0-major threshold, and substantive proof fills out of scope.

**Not yet clear to merge — root's final source verification and issue-time reconciliation remain; no pack is issued by this review.**
