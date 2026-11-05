# Gate 03f1 ([PS10] ch. 2–4, discrete log, its hard-core bit, ElGamal): external statement audit pack

**Status: draft.** The pinned head, the attestations and the bundle are filled in once the base
repair has landed (`PLAN.md`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`<HEAD, 40 hex, from git rev-parse>`. This pack covers the discrete-log candidate (the assumption
and the collection), its hard-core bit, ElGamal, and the concrete samplers they use.
- **This pack gates fills.** Its files hold **21 `sorry`s**. By the user's ruling of 2026-11-05 they
  will be filled after this pack closes, discrete log first, because ch. 5–8 cites the DL candidate
  (Thm 142.3). A statement that cannot be proved as stated, or that is weaker than the source,
  must be found **now**, before anyone tries to fill it.
- **Gate type:** an external **statement gate** (`workflow.md` §3), over a layer written in another
  campaign (Frederick Dehmel's, now closed). That layer had only an internal audit (run 3a).
- **The deliverable:** **`gate03f1-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs:
- §2.8 (book pp. 52–53);
- §3.4.1 (pp. 82–86);
- §3.11 (pp. 105–107);
- Claim 36.2 (p. 36);
- Claim 62.2 (p. 62).

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle). Also:
- For **every sorried declaration**, say whether it is (a) true as stated and provable from the
  hypotheses it carries, (b) true but stated more weakly than the source, or (c) false or
  unprovable as stated. For (c), give a counterexample or the missing hypothesis.
- The candidates are stated under an explicit hypothesis bundle for polynomial-time arithmetic
  (`Candidates/Arithmetic.lean`, decision D11; pack 03b audits the bundle itself). Say where a
  statement needs a field the bundle lacks.

Attempt at least **three adversarial instantiations**, for example:
- a group generator whose "generator" is the identity with non-negligible probability;
- a DDH instance whose exponents are not uniform;
- a hard-core-bit predictor that uses its advice to know the group.

Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/Candidates/{DiscreteLog, DiscreteLogHardcore, ElGamal, Concrete}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide) |
| Context, not under audit | `Candidates/Arithmetic.lean` (pack 03b); the files of packs 03a–03d, which these statements use |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D11; §5 the deviations register; §7 the source's errors and gaps) |
| Inventory | `briefs/pass-shelat/inventory-ch2.md`: Asm-52.2, Thm-52.3, Claim-53.2, Claim-36.2, Claim-62.2; `inventory-ch3.md`: Constr-82.b, Lem-84.1 (with .0, .1, .3, .4, .5), Alg-84.2, Alg-85.a, Asm-105.1, NT-105.a, Claim-106.a, Claim-106.b, Alg-106.2, Claim-107.a, Thm-107.3, Def-107.b |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` (P8-1, the DDH ensembles, was a run-3a blocker: check its repair) |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the factoring-based candidates (pack 03f2) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

To be filled at the pinned head:
- elaboration (a fresh replay of the closure);
- the axiom prints of this pack's headlines;
- **admissions:** the 21 `sorry`s, listed by declaration:
  - `DiscreteLog`: 6;
  - `DiscreteLogHardcore`: 7;
  - `ElGamal`: 7;
  - `Concrete`: 1;
- lint;
- interface use. The declarations cited by ch. 5–8 are `Candidates.ExpGroupGen` and
  `Candidates.DLAssumption`.

## Specific questions

1. **The DL assumption and collection (Asm 52.2, Thm 52.3).**
   - Is `DLAssumption` the source's assumption: the group (a safe-prime subgroup), the generator
     and the exponent sampled as stated, and inversion negligible for every n.u.p.p.t. adversary?
   - Is the validity bridge of `expCollection` (the generator output `dlDefaultIndex` below `n₀`, a
     run-3a repair) benign?
2. **The samplers** (`expSampler_spec`, `statClose_sampleBelowL`, `Concrete.lean`'s rejection
   sampler). Are the claimed closeness bounds negligible at the stated parameters, and are the
   specifications what the collection needs?
3. **The hard-core bit of DL (§3.4.1, Lem 84.1).**
   - Is the "half" predicate, with its inverter reduction (Algs 84.2 and 85.a), stated with the
     right advantage loss?
   - Lemma 84.1's generator is restricted to `p ≡ 3 (mod 4)` (open question 3 of Frederick's
     plan). Is that restriction declared, and is it benign?
4. **ElGamal (Asm 105.1, Alg 106.2, Thm 107.3).**
   - Is DDH stated on the right group with uniform exponents, and is P8-1's repair right?
   - Is the message space `G_q` handled as the source requires?
   - Is the encryption correct (`elGamal_correct`) for every message?
   - Is the security statement `elGamal_secure` the source's CPA security?
5. **Claim 107.a** (squaring a uniform unit is uniform on `G_q`, a generator unless it is `1`). Is
   `statClose_sq_generator` the claim, at the right distance?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. Add the column **Sorry verdict** (a / b / c, see the
brief) for sorried declarations. The pack closes at **0 blockers and 0 majors**.
