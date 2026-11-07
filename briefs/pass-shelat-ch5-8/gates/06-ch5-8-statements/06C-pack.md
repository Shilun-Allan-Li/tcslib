# Gate 06C (Pass–shelat ch. 7, composability): external statement audit pack

**Round 1: common preparation complete; ready for staging (2026-11-07).**
Audit source: `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor:
`eee107e92a7db11f1f8c98a5c2867304f57ddc54`; draft PR #232. Historical prong heads are provenance only.
This document records neither staging/user dispatch nor external gate closure. Auditor: **Codex**;
return findings Markdown in the audit chat, with no commit or push requested. The user dispatches
all four audits after reviewed bundles and external pins are staged.

**What is audited:** the trusted surface of [PS10] ch. 7 as formalized in
`TCSlib/Cryptography/Composability/`: definitions, statements, docstrings and proof sketches,
against the sources. Proofs are out of scope, except the short ones that carry a definition's
correctness (for example `correct` fields and the phase lemma of `seqRep`). The deliverable is
**`gate06C-findings.md`**.

**Sources for round 1 (receiving-auditor access must be verified):**
- [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010. Book page = PDF
  page − 12. §7.1–7.2, book pp. 167–176.
- [PSV06] Pass, shelat, Vaikuntanathan, CRYPTO 2006, LNCS 4117, pp. 271–289 (Definition 3).
- [PSV07] Pass, shelat, Vaikuntanathan, ASIACRYPT 2007, LNCS 4833, pp. 519–535 (Definitions 1–4,
  Theorems 3 and 4, Corollary 1).
- [Gol01] O. Goldreich, *Foundations of Cryptography, Volume 1*, Cambridge University Press,
  2001, Definition 4.3.1 and §4.3.4 (aborting simulation and sequential composition).
- The 3COL corollary also uses [PS10], Theorem 124.1 and Propositions 127.6 and 128.8
  (book pp. 124–129). Its negligibility source tag [Gar26, §1.2] and existing probability API
  are context; source-attachment status is recorded separately, not implied here.

Primary author versions and draft/published-edition comparison limits are in
`source-manifest.md`; Goldreich access is through official links, not redistributed copies.

## Scope

| Item | Where | State |
|---|---|---|
| Def 168.1 (CPA, CCA1, CCA2 for private-key schemes) | `Composability/Defs.lean` | defined |
| Thm 168.2 (Algorithm 99.1 is CPA- and CCA1-secure) | `PRFScheme.lean` | stated |
| Claim 169.a (Algorithm 99.1 is not CCA2-secure) | `PRFScheme.lean` | proved from an advantage-1 adversary |
| Alg 169.3 (`π′`: encrypt, then tag) and Thm 170.4 (`π′` is CCA2-secure) | `CCA2Scheme.lean` | correctness proved; Thm 170.4 stated |
| Def 171.5 (public-key CPA/CCA) and Claim 172.a (Construction 104.3 is CPA-secure) | `PublicKey.lean` | Claim 172.a proved from a stated lemma and Thm 104.4 |
| Def 172.6 (non-malleability) and Thm 175.9 (CCA2: secrecy ⇔ non-malleability) | `NonMalleable.lean` | Thm 175.9 stated |
| Def 173.7 (relation-based non-malleability) and Thm 174.8 | `SimNonMalleable.lean` | in [PSV07]'s form; both directions stated |
| Thm 175.1 (sequential composition of ZK) | `SequentialZK.lean` | generic repetition statements admitted; phase and zero-error/abort corollaries proved from public interfaces |
| Sequential 3COL corollary with explicit count | `ThreeColoring.lean` | `negligible_colSeqSound`, `colSeq_efficientProverProof_zk`; corollary uses admitted generic repetition statements |

`CCA2Scheme.lean` constructs private-key encryption. `PublicKey.lean` defines public-key
attack games and the conditional padded CPA bridge of Claim 172.a; no public-key CCA2
construction is claimed.

## Prior findings (verify the repairs)

1. **The `Dec` guard** ([Shilun-Allan-Li/tcslib#193](https://github.com/Shilun-Allan-Li/tcslib/pull/193), ch. 2–4): Algorithm 99.1's `Dec`
   refuses malformed ciphertexts. Without the guard, Thm 168.2's CCA1 half is false.
2. **`π′`'s tag covers `(r, c₁)`** (inventory erratum, Alg-169.3): tagging `c₁` alone is not
   CCA2-secure.
3. **Public-key games pad ciphertexts** (ruling): canonical padding, with non-canonical strings
   refused. Otherwise a CCA2 adversary queries a re-padding of the challenge.
4. **Non-malleability follows [PSV06] and [PSV07]** (ruling). Thm 174.8 is false as written:
   Def 173.7's simulator gets no public key, and the quantifiers of Defs 172.6 and 173.7 do not
   line up. [PSV07] shows the equivalence holds under CPA only.
5. **Thm 175.1 assumes `ProverBounded`** (ruling on Q-1): under D8, a verifier may double its
   message length each phase, so the views of a sequential repetition can grow exponentially.

## Integration repairs present for audit

- The duplicate `Protocol.ProverBounded` is deleted. The canonical definition is in
  `ZeroKnowledge/Interaction.lean`; efficient-prover proof structures expose `boundedP`.
- `PerfectZK.seqRep` is `StatZK.seqRep` at zero error, via public `perfectZK_iff`.
  `PerfectZKAbort.seqRep` uses `PerfectZKAbort.statZK` and concludes **statistical** ZK at
  error `Q(n)·2^{-n}`. The formal premise uses strict-PPT aborting simulation; bounded independent retries yield
  the error. PS10's expected-time wording is a distinct source convention; arbitrary expected-
  time truncation is not asserted to preserve an exact conditional law. Source tags are `[Gol01]`.
- The 3COL module fixes `Q(N)=2(N+1)^2`, proves negligibility of
  `(1 - 1/N + 2^{-N})^Q(N)`, and obtains its efficient-prover/computational-ZK corollary
  from `col_efficientProverProofErr`, `col_zk` and generic repetition statements. The count
  replaces the source's graph-dependent one with a declared sufficient polynomial; this
  `seqRep` schedule is not `colProtocolRep`.
- Sequential ZK uses shared `coinBlock` from `Asymptotic/Adversary.lean`. CCA2's equal-length
  padding step uses `Collection.ofFn_padFin_of_le` in `CollectionsHelpers.lean` (DL-6/DL-7).
  Public reading interfaces and topic/root exports are present. Native reconciliation is complete
  at the frozen head, with the root export not elaborated. Common collection, seals, controls and
  axiom reconciliation are complete with retained failures as detailed below. Further source repairs require an affected replay.

## Source bundle and context

Primary paths below use braces as set notation; each name has the `.lean` suffix:

- `TCSlib/Cryptography/Composability.lean`.
- `TCSlib/Cryptography/Composability/{Defs,PRFScheme,CCA2Scheme,PublicKey,NonMalleable,SimNonMalleable,SequentialZK,ThreeColoring}.lean`.

The prepared source-only bundle contains these paths' complete final-head TCSlib import closure,
plus `TCSlib.lean` for root-export context, with raw-byte hashes and revision-qualified provenance.
Shared Games/Interaction/Machines/Collections/FinDist/complexity owners are context, not new
prerequisite audits. Include the common record/evidence set specified in `PLAN.md` and retain
source-version/access limits. Do not substitute historical prong or e9 dependency copies.

## Brief for the auditor

You are auditing the **trusted surface**. Hunt for:
1. **Infidelity:** a definition or statement that differs from the source's other than by a
   declared deviation; check that each declared deviation is benign or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous hypotheses; games an adversary wins or loses for degenerate
   reasons (message length 0, an empty ciphertext space, a budget of 0).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims.
5. **Attribution:** `policy.md` §2.

For **every definition**, restate it in your own words before reading its docstring. For
**every theorem**, say in 1–3 sentences whether the statement is what its docstring claims. Attempt
at least **three adversarial instantiations**. Do not give a blanket approval.

## Specific questions

1. **The oracle games.** In `indImpl` (private and public key), is `Dec`'s availability per attack
   (`decOpen`) Def 168.1's `[Enc, Dec; Enc, Dec*]` table? Is the challenge asked at most once in
   effect (`indImpl_challenge_repeat`)? Does fixing message lengths (`FixedLengthScheme`) lose
   anything?
2. **Padding (Def 171.5).** Is `FixedLengthPKScheme` with `padCt`/`isPadded` a faithful reading
   of a public-key scheme with variable-length ciphertexts? Can an adversary exploit the
   refusal of non-canonical strings?
3. **Def 172.6.** At CPA, is `nmGame` [PSV06, Definition 3]? Under CCA, are the oracles those of
   Def 171.5? Is it right that a copy of the challenge and an invalid ciphertext are both `⊥`?
4. **Def 173.7 as SIM-NME′.** Compare `snmReal`/`snmIdeal` with [PSV07, Definition 1] at one
   message. In particular:
   - the sampler: here a sampler `M` is quantified with the adversary, and `A₁` outputs its
     parameter (with a universal clocked sampler, [PSV07]'s form). Is this equivalent?
   - the `COPY` encoding, the simulator's single query, and its lack of a `Dec` oracle;
   - the convention when no challenge is asked.
5. **Thm 174.8.** Is "under CPA, plus SIM ⇒ IND for every attack" the strongest true reading,
   given [PSV07, Theorems 3 and 4, Corollary 1]? [PSV07] defers both proofs; **check the
   maintainer's two sketches** (`nmSecure_of_simNMSecure`, `simNMSecure_of_nmSecure_cpa`) as
   arguments. Distinguish PSV06's copy-to-bottom convention from PSV07's COPY marker;
   check the complementary-pair copy-flag export and the L=0 case in the one-challenge model.
6. **Thm 175.1.** Is `seqRep` the source's `Q(n)`-phase repetition, with fresh coins per phase?
   Is canonical `ProverBounded` faithful and supplied by the efficient-prover interfaces?
   Check the abort conclusion `StatZK` at error `Q(n)·2^{-n}`. For 3COL, check the repeated
   soundness formula, eventual negligibility (including the finite `N=0` prefix), sufficient
   quadratic count, scheduling deviation, and attribution to Theorem 124.1/Propositions 127.6,
   128.8 and Theorem 175.1.

## Completed common preparation

The common evidence is reconciled at the source/base above. The final index is
`briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/FINAL-EVIDENCE.md` and its machine summary is
`briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1/FINAL-SUMMARY.json`.
The final index/common archive hashes and the records commit/bundle hashes are pinned externally
in the exchange README and dispatch prompt, outside these pack bytes.

| Common check | Completed outcome and limit |
|---|---|
| Scope/native | 61 changed Lean paths: **54 math modules + 7 import/option-only facades**. All 1,108 library sources match the snapshot; 467 native source/object/prerequisite records are reconciled after 182 affected checks. `TCSlib.lean` was **not elaborated**. |
| Full-source seals | All 54 harnesses valid: **37 source passes, 17 source failures, 138 diagnostics in 110 unchanged full header/proof blocks**. No new/touched failing block or home-induced read was identified. All failures remain failed observations. |
| Failure/debt disposition | Exact historical-key normalization gives **62 historical / 48 additional observation keys**. Additional observations are retained inherited debt, not new source violations or failure exclusions. |
| Sensitivity controls | All **11** verified: 5 unsealed negative passes, 5 sealed sole-proof failures, 1 sealed published-reader pass. |
| Axioms/admissions | **2,881 actual identities**: 2,835 standard-only, **46 admitted-dependent** (33 direct statements + 13 derived dependencies), 0 unexpected axioms. The same 46 names/dependencies remain; substantive proof completion is not claimed. |
| Source scans/C3 | **C1: 142 raw hits + 10 selected-open supplement observations; C2: 10 rows; C3: 3 retained legacy pairs**, not zero. The exhaustive TCS record has 134 inherited candidates: 131 debt + 3 exact recorded notation items. All 18 non-TCS raw hits are unchanged too. Composite new/touched review identifies **0 foreign-body violations / 0 unresolved items**. |
| Style/API | 10 inherited style findings, 0 new; each complete prong's plain/check8b runs returned 0. This is not an all-library lint or Rule10-clean claim. |

The completed C3 R2 census covers all owned types/values, including opaque/private/generated
constants; its exact per-module root sets match all 2,881 identities. Both metadata controls
pass. The private BlockEncryptor pair is an older eqn-term observation outside the 110 failed
blocks; counts are not blindly added. Invalid R1 C3 and earlier harness attempts remain labelled
invalid. No failure, notation reference or inherited read is filtered or waived.

S2's separate candidate-host fill (PR #231) is **not incorporated or attested** by this Gate06
source. Earlier closed S2a/S2b APIs remain context. Further source repairs require renewed
source-matched affected/downstream checks and audit pins.

## Round 1 source and delivery identities

| Attachment identity | Exact value |
|---|---|
| Source bundle exchange path | `outbox/gates/06C-r1-gate/gate06C-source-bundle.md` |
| Source bundle SHA-256 | `15dfbca8d2d255b5b31bd71393a8c87bd7b88946cd46c9a3a2ff32a65a34654b` |
| Source sections | 171 raw files: the 170-module primary TCSlib closure plus root-export context |
| Source-only manifest in records | `briefs/pass-shelat-ch5-8/gates/06-ch5-8-statements/06C-source-manifest.json` |
| Manifest exchange filename | `gate06C-source-manifest.json` |
| Source-only manifest SHA-256 | `f649a5fa5ff1dee8395586345f0dc1a22efab783e850f46185e7230fbfb1406b` |

The manifest contains raw source path/revision/byte/hash rows, primary modules/import closure,
source-bundle filename/hash and source/base pins only. It contains no records commit or self-hash.
`TCSlib.lean` is context, not a closure root or an elaborated export check. The exact source-only
bundle is prepared and verified; staging is an external action. A later records snapshot and its
records/common bundles are identified only by the exchange README and user dispatch prompt,
which also pin the common archive and final index. This avoids a records/hash self-reference.

Receiving auditor: verify access to the common provided exact tracked PS10 course PDF and the
required official Goldreich/PSV URLs/version notes in `source-manifest.md`; list exact unavailable
comparisons in the findings. Draft/publisher equivalence and deferred proof limits remain audit
subjects. Do not redistribute third-party PDFs, extracted full text or rendered pages.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide:
- **blocker:** a downstream phase would build on a wrong statement;
- **major:** a statement is fixable but materially misleading as it stands, or accumulated debt
  that the gate may not close over without explicit human acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The gate closes at **0 blockers and 0 majors**.

**Not yet clear to merge — external statement audits and their resolutions remain.**
