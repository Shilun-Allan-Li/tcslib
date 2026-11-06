# Gate 03d ([PS10] ch. 2–4, PRFs and encryption): external statement audit pack

**Status: draft.** The pinned head, the attestations and the bundle are filled in once the dedup
PR and the F-1 restatement have landed (`PLAN.md`; ruling of 2026-11-05: 03d waits for F-1).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`<HEAD, 40 hex, from git rev-parse>`. This pack covers secure encryption (single- and multi-message, private- and public-key), pseudorandom functions and their oracle model, and the zero-knowledge reading of encryption (§4.2).
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05),
  over a layer written in another campaign (Frederick Dehmel's, now closed). That layer had only
  an internal audit (run 3a, summary in the bundle).
- **The deliverable:** **`gate03d-findings.md`**, committed as `inbox/gate03d-findings.md` on the exchange branch `exchange/pass-shelat-ch5-8` and pushed (the protocol is that branch's `README.md`: write only that file, `git pull --rebase` before pushing, never force-push, no PR).

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source** is [PS10], 3rd ed., January 2010: `Pass–Shelat.pdf` at the root of `cryptography/pass-shelat-ch2-4` (SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`). Book page = PDF
page − 12. This pack needs §2.1.3 (Def 24.7, book p. 24), §3.5–§3.10 (pp. 91–105) and §4.2 (pp. 110–112).

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle): the trusted surface, the six
things to hunt for, the inventory check, restating every definition in your own words, and 1–3
sentences per theorem. Attempt at least **three adversarial instantiations**, for example:
- an oracle adversary that queries outside the domain, or adaptively at exponential length;
- a "secure" scheme whose correctness fails on a negligible but nonzero set of keys;
- a public-key scheme whose adversary does not receive the public key.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Asymptotic/{PRF, Encryption, MultiMessage, PublicKey, BlockEncryptor}.lean`, `TCSlib/Cryptography/ZeroKnowledge/Encryption.lean`; and, restated by item F-1 (`design/F1-oracle-restatement.md`), the concrete layer's `TCSlib/Cryptography/Pseudorandom/Functions/{OracleAdversary, LazySampling}.lean` and `TCSlib/Cryptography/Games/Bridges/QueryTree.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide; its questions are not this pack's) |
| Context, not under audit | packs 03a–03c's files: earlier packs of this gate |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D1–D11, §2.13 and §2.14 the frozen shapes, §5 the deviations register) |
| Inventory | `briefs/pass-shelat/inventory-ch3.md`: Def-91.1, Alg-92.1, Claim-92.a, Thm-92.2, Def-93.1, Thm-94.2, Def-96.1, Claim-96.a–c, Def-96.2, Cor-97.a, Claim-97.c, Thm-97.3 (and .3), Alg-99.1, Thm-99.2 (with .1–.3), Def-102.1, Def-102.2, Claim-103.a, Claim-103.b, Def-103.c, Thm-103.d, Def-103.e, Thm-103.f, Constr-104.a, Alg-104.3, Lem-104.a, Thm-104.4; `inventory-ch2.md`: Def-24.7; `inventory-ch4.md`: Def-111.1, Def-111.a, Def-111.b, Thm-112.2 (with .i, .ii), Claim-112.a, Claim-112.b |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (`Pass–Shelat.pdf`, campaign branch root) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the GGM reduction and the encryption lemmas (`GGMReduction*`, `PRFLemmas`, `MultiMessageLemmas`, `PublicKeyLemmas`), whose statements pack 03j audits |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

To be filled at the pinned head:
- elaboration (a fresh replay of the closure);
- the axiom prints for this pack's headline theorems (`audits/pass-shelat/Checks.lean`);
- admissions: none in these six files;
- lint;
- interface use. The declarations cited by ch. 5–8 are `PRF` (its security is the field `pseudorandom`), `PRF.negligible_prfAdv`, `OracleEnsemble`,
  `OracleEnsemble.Indist`, `OracleMove`, `prfAdv_toOracleAdversary`, `PrivateKeyScheme`,
  `SingleMessageSecure`, `MultiMessageSecure`, `prfScheme`, `prfScheme_multiMessageSecure`,
  `PublicKeyScheme`, `BitPublicKeyScheme`, `tdpBitScheme` and
  `TrapdoorCollection.tdpBitScheme_singleBitSecure`. **Restated before this pack (item F-1):**
  `QueryTree` is the one-oracle `Games.OracleComp`, so `OracleEnsemble.Indist`'s adversaries are
  framework computations, and `NUPPT.toOracleAdversary` is an instance of the generic decoder
  `NUPPT.toComp`. Check that the restatement changed no meaning.

## Specific questions

1. **Oracle ensembles and PRFs (Defs 96.1, 96.2).**
   - Is `OracleEnsemble.Indist` "every n.u.p.p.t. oracle machine distinguishes `f_s` from a
     random function with negligible advantage"?
   - Is the random function lazily or eagerly sampled, and is it uniform over all functions of
     the right length?
   - Is the query model (`OracleMove`) adaptive, and bounded by the machine's running time?
2. **GGM (Thm 97.3).** Is the statement "a PRG gives a PRF family" at the right strength, with the
   right key, input and output lengths?
3. **Single-message security (Defs 91.1, 24.7; Thms 92.2, 94.2).**
   - Is the indistinguishability game the source's, with messages chosen per `n` by the adversary?
   - Is correctness exact or overwhelming, and does it match?
4. **Multi-message security (Def 93.1; Alg 99.1, Thm 99.2).**
   - Is the number of messages polynomial and adversarially chosen?
   - Is the §3.9 scheme `r ‖ m ⊕ f_k(r)` stated with fresh `r` per message?
5. **Public-key encryption (Defs 102.1, 102.2; Alg 104.3, Thm 104.4).** Does the adversary get
   `pk`? Is the bit-encryption scheme from a TDP with a hard-core bit stated as the source has it?
6. **Zero-knowledge encryption (Def 111.1, Thm 112.2).** Is the simulator's quantifier order
   right, and are both directions stated?
7. **`BlockEncryptor.lean`** has no inventory row. Say what it is for and whether its statements
   are true and correctly attributed.

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.
