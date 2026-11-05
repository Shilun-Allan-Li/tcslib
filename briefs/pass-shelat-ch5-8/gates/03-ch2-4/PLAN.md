# Gate 03: the external statement gate of ch. 2–4 (plan)

- **Ruling (user, 2026-11-05):** full, interface first. Frederick's campaign had only an internal
  statement audit (run 3a, `audits/pass-shelat/run3-audit-summary.md`); `workflow.md` §3 requires
  an external one, by a different vendor.
- **What is audited:** the trusted surface of the asymptotic layer of [PS10] ch. 2–4 on
  `cryptography/pass-shelat-ch2-4`: definitions, statements, docstrings and proof sketches,
  against the source. About 52,900 lines in 93 files; the 13 packs below cover every one (checked by script). Proofs are out of scope.
- **Not audited here:** the four directories inherited from the Garg ch. 1–3 campaign
  (`Foundations`, `OneWayFunctions`, `HardcoreBit`, `Pseudorandom`), which were audited there
  (`audits/garg-ch1-3/`). `Foundations/Negligible.lean` comes as context.
- **The pinned head:** the branch after the base repair and the `main` merge
  ([Shilun-Allan-Li/tcslib#186](https://github.com/Shilun-Allan-Li/tcslib/pull/186)), so that every
  pack audits a commit that builds.
- **Every pack carries:**
  - Frederick's design record, `briefs/pass-shelat/DESIGN.md`: the frozen decisions D1–D11, the
    frozen signatures, and the deviations register in its §5;
  - the inventories of the chapters it covers (`briefs/pass-shelat/inventory-ch{2,3,4}.md`);
  - the run-3a summary, so the auditor can check the repairs instead of re-finding them;
  - `policy.md`;
  - the PDF.

## Packs, in dispatch order

**Interface packs.** These declarations are cited by ch. 5–8 (the S1 note's interface list). They
go first, because a statement change here would ripple into ch. 5–8.

| Pack | Content | Files | Lines |
|---|---|---|---|
| 03a | machines and probability | `Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}`; `Asymptotic/{Adversary, Sampling, Ensembles}`; context: `Foundations/Negligible` | ≈ 3,800 |
| 03b | one-wayness and collections | `Asymptotic/{OneWay, Collections, Permutations}`, `Candidates/Arithmetic` | ≈ 2,700 |
| 03c | hard-core bits and PRGs | `Asymptotic/{Pseudorandom, NextBit, HardCore, HardCoreClaims}` | ≈ 2,200 |
| 03d | PRFs and encryption (after the F-1 restatement, ruled 2026-11-05) | `Asymptotic/{PRF, Encryption, MultiMessage, PublicKey, BlockEncryptor}`, `ZeroKnowledge/Encryption`; restated by F-1: `Pseudorandom/Functions/{OracleAdversary, LazySampling}`, `Games/Bridges/QueryTree` | ≈ 4,400 |
| 03e | interaction and ZK definitions | `ZeroKnowledge/{Interaction, InteractiveProofs, Defs, Commitment, NP}` | ≈ 2,700 |

**Sorried statements.** Each must close before its fills are issued.

| Pack | Content | Files | `sorry`s | Lines |
|---|---|---|---|---|
| 03f1 | discrete log, its hard-core bit, ElGamal | `Candidates/{DiscreteLog, DiscreteLogHardcore, ElGamal, Concrete}` | 21 | ≈ 2,700 |
| 03f2 | factoring, RSA, Rabin; number theory | `Candidates/{Factoring, RSA, Rabin}`, `NumberTheory/*` | 36 | ≈ 4,900 |
| 03g | 3-colouring ZK | `ZeroKnowledge/ThreeColoring/*` and its facade | 3 | ≈ 5,900 |
| 03h | ch. 2 results and the universal OWF | `Asymptotic/{OneWayLemmas, OneWayYao, Universal, UniversalLemmas, UniversalPadding, CollectionsLemmas}` | 2 | ≈ 3,800 |

**The rest.**

| Pack | Content | Files | Lines |
|---|---|---|---|
| 03i | Goldreich–Levin and hard-core results | `Asymptotic/{HardCoreLemmas, HardCoreLoops, HardCoreGL, HardCoreGLColl, HardCoreGLFamily, GoldreichLevinDomain, HardCorePermutation, EnsemblesLemmas}` | ≈ 4,600 |
| 03j | GGM, PRF and encryption results (after F-1, which touches these files) | `Asymptotic/{GGMReduction, GGMReductionEval, PRFLemmas, MultiMessageLemmas, PublicKeyLemmas}` | ≈ 3,600 |
| 03k | graph isomorphism ZK and encodings | `ZeroKnowledge/{GraphIsomorphism*, GraphIsomorphismZK*, Encoding*, CommitmentLemmas, NPLemmas}` | ≈ 9,300 |
| 03l | machine infrastructure (last; internally verified in run 3b) | `Complexity/Randomized/Build/*` | ≈ 3,200 |

- **Dispatch.** Packs within a row group may run in parallel.
- **Triage.** Each findings file gets a review sub-agent, then resolutions. A pack closes at
  0 blockers and 0 majors.
- **Repairs to statements cited by ch. 5–8** are re-synced there in the same PR.

## Raised with the user (settled)

The branch carries pdftotext extracts of ch. 2–4 and the appendix
(`blueprint/src/references/pass-shelat-2010-*.raw.md`). Settled by the ruling of 2026-11-05: [PS10]'s
text follows `policy.md` §2, ingested at the main landing.

## Drafts

All 13 packs are drafted (`03a-pack.md` to `03l-pack.md`). The dedup (#192) and the `Dec` guard
(#193) have landed, so 03a–03c, 03e–03i, 03k and 03l pin to the merged head
`a3c5fa8b72e50939822f22364647dc844a3914a0`, after a fresh replay there (in progress, 2026-11-05).
03d and 03j pin when the F-1 restatement (S2b) lands.
