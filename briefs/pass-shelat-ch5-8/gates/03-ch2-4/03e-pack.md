# Gate 03e ([PS10] ch. 2–4, interaction and ZK definitions): external statement audit pack

**Status: draft.** The pinned head, the attestations and the bundle are filled in once the dedup
PR has landed (`PLAN.md`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`<HEAD, 40 hex, from git rev-parse>`. This pack covers the interaction model (strategies, executions, views, protocols), interactive proofs, the zero-knowledge definitions, commitments, and the NP layer used by Thm 124.1.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05),
  over a layer written in another campaign (Frederick Dehmel's, now closed). That layer had only
  an internal audit (run 3a, summary in the bundle).
- **The deliverable:** **`gate03e-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §4.4–§4.7 (book pp. 114–127) and the appendix definition Def 191.11.

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle): the trusted surface, the six
things to hunt for, the inventory check, restating every definition in your own words, and 1–3
sentences per theorem. Attempt at least **three adversarial instantiations**, for example:
- a verifier that is efficient but reads exponentially long messages;
- a "proof" whose soundness holds only because the verifier's verdict is ill-defined;
- a simulator that is efficient only because the auxiliary input is bounded.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/ZeroKnowledge/{Interaction, InteractiveProofs, Defs, Commitment, NP}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide; its questions are not this pack's) |
| Context, not under audit | packs 03a–03d's files: earlier packs of this gate |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D1–D11, §2.15 the frozen ch. 4 signatures (with D8, the interaction reading), §5 the deviations register) |
| Inventory | `briefs/pass-shelat/inventory-ch4.md`: Def-114.a, Def-114.b, Def-115.a–d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-117.b, Claim-117.c, Def-119.5, Def-119.e, Def-191.11, Def-121.1, Def-121.2, Def-122.a, Claim-122.b, Def-124.a, Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b–d |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the protocols and their proofs (graph isomorphism, 3-colouring: packs 03g and 03k) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

To be filled at the pinned head:
- elaboration (a fresh replay of the closure);
- the axiom prints for this pack's headline theorems (`audits/pass-shelat/Checks.lean`);
- admissions: none in these five files;
- lint;
- interface use. The declarations cited by ch. 5–8 are `Strategy`, `View`, `Protocol`, `InteractiveProof`, `ZK`, `PerfectZK`, `PerfectZKAbort` and
  `Commitment`. **Context for the auditor:** ch. 5–8 runs protocols in a new framework, through a
  bridge to these definitions (`Party.exec`, under D8's reading). The ruling of 2026-11-05 carries
  D8's strict or truncated simulators into the sequential composition of ch. 7.

## Specific questions

1. **The interaction model (Defs 114.a–116.b; D8).**
   - Is the fixed-alternation reading of D8 (the next-message function on the complete history is
     the output; a halting party sends `[]`) benign for every use in ch. 4?
   - Is the verdict convention (P9-3: the verifier's last message is its verdict when it moves
     last) a restriction that excludes any protocol of the source?
2. **Efficiency (Def 116.b).**
   - `Strategy.Efficient` is polynomial in the total input length, with `ReadsPrefix` restoring
     the bound in `|x|`. Is that faithful to "time `t(|x|)` regardless of messages"?
   - Is `ReadsPrefix` required wherever the source needs it?
   - **Known consequence (maintainer, 2026-11-05).** `ZK` quantifies over `Strategy.Efficient`
     verifiers without `ReadsPrefix`. Such a verifier may double its messages from activation to
     activation, so over polynomially many rounds, against an honest prover that echoes it, its
     view can grow exponentially, and no strict-PPT simulator can output it. Ch. 5–8's sequential
     composition (Thm 175.1) therefore assumes bounded honest-prover messages
     (`Protocol.ProverBounded`). Does any ch. 2–4 ZK theorem depend on this gap? The honest
     provers of the graph protocols have fixed message lengths. Should `ZK` itself require
     `ReadsPrefix` of `V*`? (Queued for the user as Q-1.)
3. **Interactive proofs (Def 116.1).** Are completeness and soundness stated against every
   (unbounded) prover, with the source's error bounds?
4. **Zero knowledge (Defs 121.1, 121.2, 122.a).**
   - Are `ZK` (every n.u.p.p.t. `V*` with auxiliary input), `PerfectZK` and the statistical form
     faithful?
   - D8 uses strict PPT simulators where the source has expected polynomial time. Is
     `PerfectZKAbort` (truncation with abort) an adequate stand-in for the source's perfect ZK
     protocols?
5. **Commitments (Def 126.3, Thm 126.4, Alg 127.a).** Are hiding and binding at the source's
   strength (computational hiding, perfect binding), and is the OWP-based scheme stated correctly?
6. **NP and Levin reductions (Def 124.a, Def 191.11; `NP.lean`).** Is the NP relation (efficient
   verifier, polynomially bounded witness) and the witness-preserving reduction the one
   Thm 124.1's form (A) needs?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.
