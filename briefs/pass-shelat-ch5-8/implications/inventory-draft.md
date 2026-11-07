# Implications inventory — draft contents by primitive

**2026-11-07 PST.** Source-level inventory reviewed by an internal maintainer agent.
No fresh combined axiom sweep was run for this inventory. “Source-level proved” means the
inspected route is implemented; it does not certify an unexamined composition or erase its
hypotheses. Gate 06 rows refer to the unmerged integration worktree. Proposed wrapper names
and source references will be pinned and elaborated before a Lean PR.

Existing existential endpoint theorems should be imported/documented or re-exported rather
than copied under new names without a benefit. Add a short wrapper where it exposes a missing
end-to-end witness or composes a useful chain. All names below are relative to
`TCSlib.Cryptography`.

| Primitive | Existing endpoint / source | Retained premises | Current status and intended Implications contents |
|---|---|---|---|
| PRG | `exists_securePRG_of_owp`, `Asymptotic/HardCorePermutation.lean` | `∃ P : PermFamily, OneWayPermutation P` | Source-level proved. Index the OWP → Goldreich–Levin → secure PRG chain; preserve OWP rather than claiming arbitrary OWF. |
| PRF | `exists_prf_of_exists_prg`, `Asymptotic/PRF.lean` | Existence of a secure PRG | Source-level proved. Compose with the OWP theorem for an explicit OWP → PRF existence endpoint. |
| Private-key encryption | `exists_multiMessageSecure_of_prf`, `_of_exists_prg`, `Asymptotic/MultiMessage.lean` | PRF or secure PRG existence | Source-level proved. Reuse these and add the short OWP → multi-message private-key encryption composition if useful. Keep SingleMessageSecure/MultiMessageSecure names exact. |
| Public-key encryption | Hard-core-TDP → single-bit; bitwise → `PublicKeyScheme.Secure`; multi-message theorem, `Asymptotic/PublicKey.lean` | TDP one-wayness and ordinary hard-core security; GL path additionally needs exact `henc` | Source-level proved generic components. Draft in `public-key-draft.md`. Exact Gate 06 CPA bridge remains admitted; RSA/Rabin normalization is a real gap. |
| MAC | `Authentication.prfMAC_secure`, `Authentication/PRFMAC.lean` | `PRF F`; efficient evaluator and its agreement equation (obtainable from PRF.easy) | Admitted, Gate 06A. Plan a PRF → secure MAC existential, then OWP/PRG compositions once the security theorem is gated and filled. |
| One-time signatures | `Authentication.lamport_oneTimeSecure`, `Authentication/Lamport.lean` | `(lamportOWF L f).StrongOneWay`, `n`-bit inputs, efficient agreeing evaluator | Admitted, Gate 06A. Candidate collections give arbitrary input polynomials; a genuine normalization bridge is needed to instantiate this interface. No many-query signature theorem found. |
| Collision-resistant hashing | `Authentication.dlHash_crh`, `Authentication/DLHash.lean` | ArithmeticFP, ExpGroupGen validity, full-group order `m=p−1`, DL hardness | Admitted, Gate 06A. Existing safe-prime subgroup DLAssumption does not discharge full-group order; record separate assumption/model requirements. |
| Hash-and-sign | `hashAndSign_oneTimeSecure`, `exists_oneTimeSecure_of_crh_owf`, `Authentication/HashAndSign.lean` | Globally full CRH domain, collision resistance, matching hash/signature lengths; existential route needs hash output length n | Proved modulo Gate 06A admissions. The current dlHash domain is restricted, so it cannot supply the full-domain premise. Preserve one-time security. |
| Commitments | `exists_commitment_of_owp`, `ZeroKnowledge/Commitment.lean` | OWP existence | Source-level proved. Endpoint is perfectly binding and computationally hiding Commitment. Reuse the existing existential theorem. |
| 3COL zero knowledge | `col_zk`, `col_zeroKnowledgeProof`, `ThreeColoring/Simulator.lean`; new `Composability.colSeq_efficientProverProof_zk` | Commitment | Existing source-level proved result keeps one-run computational ZK and a separate repeated negligible-soundness protocol. The new same-sequential-protocol corollary is proved modulo Gate 06C composition admissions. Distinguish the protocols explicitly. |
| NP zero knowledge | `zk_proof_of_witnessRelation_of_owp`, `ZeroKnowledge/NP.lean` | OWP existence, WitnessRelation L R, **LevinNPHard L3COL R3COL** | Source-level proved conditional wrapper; LevinNPHard premise is not formalized. Keep this cost visible; retain the separate-protocol distinction above. |
| Oblivious transfer | `otProtocol_hbcSecure`, `SecureComputation/ObliviousTransfer.lean` | T.OneWay, **EnhancedHardCore** with sampler coins exposed, polynomial evaluator H correct on encodings | Proved modulo two Gate 06B admissions. Ordinary hard-core security does not supply the enhanced property; no candidate bridge found. |
| Secure two-party computation | `yaoProtocol_hbcSecure`, `SecureComputation/YaoReal.lean` | Uniform fan-in-two circuit family with sink outputs; two efficient PRFOut families jointly pseudorandom under the same key; OT premises | Proved modulo Gate 06B admissions. Endpoint is honest-but-curious security, not malicious security. |

## Bridges that must not disappear in the composition layer

- RSA/Rabin → GL padding: the current exact encoding-length premise is not satisfied by the
  candidate parameterizations. Design a real generalized/per-index padding or normalization
  bridge before a candidate-level PKE existence theorem.
- ElGamal → a generic PKE record/security game: its existing endpoint is GroupPKScheme.Secure;
  carry its separate admissible-message correctness statement and any conversion explicitly.
- Collection one-wayness → Lamport's input length: `Collection.OneWay.exists_strongOneWay`
  yields an arbitrary polynomial input length, not automatically n. No candidate-collection
  → PermFamily bridge was found in this survey.
- Subgroup DL → full-group hash assumptions, and restricted-domain CRH → full-domain
  hash-and-sign, each need separate work; the existing hypotheses do not compose.
- Ordinary hard-core → enhanced hard-core with exposed sampler coins is not an existing bridge.
- Source one-time, many-message, non-uniform, computational/statistical and protocol-model
  distinctions survive unchanged in the high-level endpoints.

## First implementation slice

1. Index the existing generic public-key chain. Add the minimum useful existential entry point
   (optionally the final multi-message result), checked against exact APIs and full axioms.
   PK-1–PK-4 describe the existing levels; they are not four required new proof tasks.
2. OWP → PRF and OWP → multi-message private-key encryption, composed from existing proved
   existential results; document/re-export existing endpoints rather than duplicating them.
3. Add the admitted Gate 06 families only as their statement gates/fills close. A small wrapper
   with a dependency on sorryAx remains an unfinished implication in the index.
4. Handle the substantial bridge list through separate public design/gate/fill tasks. Ask the
   user for the worker choice before preparing an external audit/fill; none is issued here.

**Not yet clear to merge — draft inventory; missing bridges and Gate 06 admissions remain.**
