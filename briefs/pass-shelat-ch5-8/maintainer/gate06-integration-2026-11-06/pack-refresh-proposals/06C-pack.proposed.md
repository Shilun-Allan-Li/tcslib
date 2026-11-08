# Gate 06C (Pass–shelat ch. 7, composability): external statement audit pack

**Status: unissued DRAFT (2026-11-07); not staged or dispatched.** Frozen integration source:
`3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor:
`eee107e92a7db11f1f8c98a5c2867304f57ddc54`; draft PR #232. This is not an issued audit pin.
The 467-module native union is source/object/prerequisite reconciled with zero stale records
after 180 + 2 affected checks; `TCSlib.lean` was not elaborated. The fresh collector is active;
fresh whole-file seals, controls and final axiom outcomes are not yet available. Historical
prong heads are provenance only. Auditor: Codex; findings Markdown in the audit chat; the user
dispatches the job. No readiness or final seal-pass attestation is made here.

**What is audited:** the trusted surface of [PS10] ch. 7 as formalized in
`TCSlib/Cryptography/Composability/`: definitions, statements, docstrings and proof sketches,
against the sources. Proofs are out of scope, except the short ones that carry a definition's
correctness (for example `correct` fields and the phase lemma of `seqRep`). The deliverable is
**`gate06C-findings.md`**.

**Sources required at issue (receiving-auditor access is not yet attested):**
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
  at the frozen head, with the root export not elaborated; the fresh collector is active and fresh
  seal/control outcomes remain pending. Further source repairs require an affected replay.

## Source bundle and context (draft; not assembled)

Primary paths below use braces as set notation; each name has the `.lean` suffix:

- `TCSlib/Cryptography/Composability.lean`.
- `TCSlib/Cryptography/Composability/{Defs,PRFScheme,CCA2Scheme,PublicKey,NonMalleable,SimNonMalleable,SequentialZK,ThreeColoring}.lean`.

The bundle must contain these paths' complete final-head TCSlib import closure, plus
`TCSlib.lean` for root-export context, with raw-byte hashes and revision-qualified provenance.
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

## Pending issue-time attestations

These are explicit issue-time fields, not completed attestations. Common evidence and the
current native/static/style limits are in `PLAN.md`.

- Issued source: `[ISSUE_SOURCE_COMMIT]` (must match the frozen head above, or receive a new
  source-matched verification); actual comparison/target disposition: `[ISSUE_BASE_DISPOSITION]`;
  records: `[ISSUE_RECORDS_COMMIT]`.
- Exact source bundle: `[ISSUE_06C_BUNDLE_PATH]`, `[ISSUE_06C_BUNDLE_SHA256]`;
  matching manifest: `[ISSUE_06C_MANIFEST_PATH]`, `[ISSUE_06C_MANIFEST_SHA256]`.
- Final source/native evidence: `[ISSUE_FINAL_EVIDENCE_INDEX_PATH]`,
  `[ISSUE_FINAL_EVIDENCE_INDEX_SHA256]`; retain the root-export non-elaboration limit and all
  affected/downstream rechecks required by any later repair.
- Fresh collector, actual axiom identities and dispositions: `[ISSUE_COLLECTOR_AXIOM_EVIDENCE]`,
  `[ISSUE_COLLECTOR_AXIOM_OUTCOMES]`. Current prepared scope is 54 mathematical modules and seven
  separately verified import/option-only facade/export files; derive scope from pinned metadata.
- Fresh full seals/controls: `[ISSUE_SEAL_CONTROL_EVIDENCE]`, `[ISSUE_SEAL_CONTROL_OUTCOMES]`.
  Cover stored types/values/private/generated declarations and anonymous commands through the
  full import-closure supplement, without name exclusions beyond approved notation. Classify
  every source failure against the actual base; inherited failures remain failed observations,
  not seal passes, exclusions or automatic waivers. Invalid harnesses remain separately labelled.
- Final explicit-unfold/source/API scans and precise existing style exceptions:
  `[ISSUE_SCAN_API_STYLE_EVIDENCE]`, `[ISSUE_SCAN_API_STYLE_DISPOSITIONS]`. Lexical census and
  parser rows do not replace elaborated axiom/declaration identities.
- Receiving auditor's source access and exact version/comparison limits:
  `[ISSUE_SOURCE_ACCESS_DISCLOSURE]`; preserve `source-manifest.md`'s linked-source arrangement.

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

**Not yet clear to merge — fresh verification outcomes, source-access disclosures, issue-time pins/bundles and user dispatch remain.**
